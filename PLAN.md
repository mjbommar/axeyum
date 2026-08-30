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
| 2026-08-30 | int-sign-product | New `int_prelude/sign_product.rs`: `Int.mul_pos_iff`, `Int.mul_neg_iff`, `Int.mul_nonneg_iff`, `Int.mul_nonpos_iff`, `Int.mul_nonneg_of_nonneg_or_nonpos`, all built from one sign case-split; 5 facts flipped open->proved |
| 2026-08-30 | totient-mult-finish | `Nat.totient_coprime_totient_iff` (closed, `F:ml430-nat-totient-coprime-totient-iff-3932cf83` flips to proved) and `Nat.coprime_mul_of_coprime` (new, axiom-free, the first of the multiplicative formula's two weakest steps — route (b), the prime-divisor contrapositive via `coprime_of_forall_prime_dvd`+`euclid_lemma`, worked first try and needed no Bézout algebra) landed and verified. `Nat.count_range_row_major` (the second weak piece, the genuinely novel row-major double-counting induction) and the three facts needing the full multiplicative formula remain open, per this task's own "don't force the formula" guidance. |
| 2026-08-30 | queue-sweep | No fact closed. All three assigned non-sign dispatchable facts (`totient_dvd_of_dvd`, `totient_gcd_mul_totient_mul`, `eq_or_eq_of_totient_eq_totient`) declined for this session: correctly-stated Mathlib mirrors this kernel does not yet have the general multiplicative-function theory to prove, distinct from the divergence-registry category. Corrected a false numerical claim in `301-totient-multiplicative.md`'s Step 4 (`count_range_row_major` is NOT coprimality-independent — fails at every tested non-coprime pair, e.g. `totient(4)=2 ≠ totient(2)*totient(2)=1`), which would have sent the next totient lane at a statement a sound kernel cannot admit. |
| 2026-08-30 | `370a51a64` | draft: `rat_prelude/cas_geometry_frac_bridge_tests.rs` -- `rat_lit` cast, `prove_scale_rat`/`prove_merge_rat`/`prove_const_combination_rat`, medians-concurrent reconstruction (compiles, not yet test-run in that commit) |
| 2026-08-30 | (pending) | tests green (11/11 sweep), mutation-verified both halves through different guards; `F:geometry-medians-cofactor-identity-kernel-checked` registered, `cas-certificate` kernel-reconstructed 9 -> 10 |
| 2026-08-30 | ipc-provable | Slice 2: `FormulaList` + `Provable` (11-constructor IPC natural-deduction inductive) over `ipc_heyting.rs`'s `Formula`, plus two kernel-checked example derivations and a non-kernel finite-search non-vacuity check; `F:excluded-middle-not-intuitionistic` stays open, needing slices 3 (generic `eval`) and 4 (soundness) |
| 2026-08-30 | ipc-eval | Slice 3: generic `eval : Formula -> (Nat -> Nat) -> Nat` as a genuine `Formula.rec` application over `ipc_heyting.rs`'s connectives, with a discriminating evaluation test suite (not merely admission) pinning its meaning; cross-checked against the existing countermodel theorem; `F:excluded-middle-not-intuitionistic` stays open, needing slice 4 (soundness) |
| 2026-08-30 | totient-mul | `Nat.gcd_mod_left_eq_gcd` and `Nat.coprime_mul_iff` (both new, axiom-free, `301`'s Steps 1 and 3 toward `totient_mul_of_coprime`) landed and verified in a new file `nat_prelude/totient_mul_coprime.rs`. Did not attempt `totient_mul_of_coprime` itself or the CRT-bijection route `316-queue-sweep.md` correctly identified as replacing `301`'s false `count_range_row_major` claim — sized as several more dispatches (a new "`countRange` invariant under a domain bijection" primitive is the largest missing piece, on top of the already-existing `nat_prelude/crt.rs` self-map). |
| 2026-08-30 | `f781973b9` | draft: `rat_prelude/cas_partial_fractions_bridge_tests.rs` -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `24c5e1eb7` | feat: kernel-reconstruct `F:cas-partial-fractions-mixed-general-case` (compiles, 4/4 tests green, both mutation guards verified) |
| 2026-08-30 | `d2a954587` | fix: clippy `doc_markdown` unbalanced backticks |
| 2026-08-30 | `f07c07346` | fact: register `F:cas-partial-fractions-mixed-general-case-kernel-checked`, `cas-certificate` kernel-reconstructed 10 -> 11 |
| 2026-08-30 | ipc-soundness | Slice 4: `ipc_ctx_meet` + `ipc_sat` (both `FormulaList.rec`), nine chain lemmas, and `ipc_soundness` by an eleven-case `Provable.rec` induction — the first use of that recursor — closing `F:excluded-middle-not-intuitionistic` (open since 2026-08-14) with `ipc_excluded_middle_not_provable`, axiom-free, plus a fail-on-absence checker example. Soundness runs on the context MEET, not on `sat`: the sat-shaped statement does not carry the induction through `imp_intro`. |
| 2026-08-30 | golden-lean-check | Added `*_module_checks_in_real_lean` to `quant_affine_growth_lean`, `quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean` (real Lean 4.30.0 crosscheck via `lean_probe`, matching `diophantine_lean_reconstruct`'s existing pattern); no pin constants touched. |
| 2026-08-30 | golden-lean-check | Wired the four new suites into `scripts/check-lean-gate.sh`'s suite list and raised `CHECK_FLOOR` 219 -> 223. |
| 2026-08-30 | `9ae10bb01` | draft: `rat_prelude/cas_geometry_pair_bridge_tests.rs` -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `0859c3992` | fix: module now compiles (missing `NatOps` import, `axiom_footprint`'s real `Vec<NameId>` return type) |
| 2026-08-30 | `b2d42508f` | fix: numeric checks -- wrong assumption about WHERE fractions live per certificate, plus a vacuous negative control |
| 2026-08-30 | `4f45e630a` | feat: kernel-reconstruct both certificates; register both sibling facts; `cas-certificate` kernel-reconstructed 11 -> 13 |
| 2026-08-30 | nat-modeq-mirrors | `nat_prelude/modeq_add_cancel.rs`: 5 new theorems + 1 pre-existing flip close 6 `ml430-nat-modeq` mirrors (add, add_iff_left/right, add_left/right_cancel, cancel_left_of_coprime); 4 left open (add_le_of_lt, 3x cancel-div-gcd) with precise blockers recorded above |
| 2026-08-30 | `b410fb749` | New `nat_prelude/gcd_dvd_mirrors.rs`: seven theorems, one `declare_*` call. |
| 2026-08-30 | `c20464d53` | Register the seven in `theorem_names`, recount `the_build_is_deterministic` pin. |
| 2026-08-30 | `935dde5e2` | Close nine ml430 facts (two flips, seven new) + depends_on cascade fix (24 files). |
| 2026-08-30 | `d92fb202d` | `div_gcd_pos_of_pos_{left,right}` — two more theorems, shared helper. |
| 2026-08-30 | `126aee313` | Close the two `div_gcd_pos_of_pos_*` facts + depends_on fix. |
| 2026-08-30 | `d255ef6e2` | rustfmt fix. |
| 2026-08-30 | `e91e718a0` | draft: `cas_geometry_bridge_tests.rs` thales addition + varignon exclusion doc -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `28a77b5c9` | feat: kernel-reconstruct thales cofactor identity, full disclosure of its refl-shaped obligation; register `F:geometry-thales-cofactor-identity-kernel-checked`; `cas-certificate` kernel-reconstructed 13 -> 14 |
| 2026-08-30 | ADR-0623 | Every gate step is time-bounded, and a cap must be proved to fire. Per-step caps in `check.sh` with a third outcome; `--kill-after` plus an explicit process-group kill in both aggregate gates; the ledger sweep bounded per-row, per-tree and whole-sweep; `scripts/check-gate-step-timeout.sh` registered in `check.sh` and the justfile. |
| 2026-08-30 | `f93339c90` | New `int_prelude/dvd_gcd_mirrors.rs` draft (not yet compiled). |
| 2026-08-30 | `3d10a5644` | Fix E0499 double-mutable-borrow; `cargo check` passes. |
| 2026-08-30 | `13447b182` | Register 11 new declarations in `derived_laws`, recount pin 196 -> 207. |
| 2026-08-30 | `c30820148` | Close 13 ml430 facts (2 flips, 11 new) + `depends_on` cascade fix. |
| 2026-08-30 | `290cb422f` | Unconditional `Int.ModEq.mul` (`mod_eq_mul_general`); recount pin 207 -> 208. |
| 2026-08-30 | `9279ffe52` | Close `F:ml430-int-modeq-mul-6736aa2e` + `depends_on` cascade fix. |
| 2026-08-30 | `9a773bac4` | wip: `Nat.gcd_mul_right` proof term, not yet registered in coverage list. |
| 2026-08-30 | `dcd876d2c` | `Nat.gcd_mul_right` admitted, axiom-free, registered, tested (concrete + symbolic). |
| 2026-08-30 | `4b9d27239` | New `nat_prelude/gcd_mul_right_mirrors.rs`: all three ml430 mirrors, registered, tested. |
| 2026-08-30 | `52dbe8dad` | Flip the three facts to `proved` + `depends_on` cascade fix (3 files). |
| 2026-08-30 | `96dd8d93a` | wip: Int transport of gcd-scaled dvd mirrors, compiles but not yet run. |
| 2026-08-30 | `e75823399` | Close all 4 facts (3 Int gcd-scaled dvd + 1 Nat dvd_add_iff_left), evidence + depends_on. |
| 2026-08-30 | `932812b9c` | wip: `modeq_cancel_div_gcd.rs` Nat family (3 mirrors), not yet compiled. |
| 2026-08-30 | `82752e56e` | Nat family admitted, axiom-free, registered, tested (concrete discriminating + symbolic); fixed a `mul_assoc` direction bug found via `Kernel::render_lean`. |
| 2026-08-30 | `590477e33` | Flip the three Nat facts + `depends_on` cascade fix (3 files). |
| 2026-08-30 | `6ec2edf6f` | wip: `modeq_cancel_div_gcd.rs` Int family (2 mirrors), compiles. |
| 2026-08-30 | `30cb26f7a` | Int family admitted, axiom-free, registered, tested; new `Int.mul` cancellation-by-nonzero lemma (first in this development). |
| 2026-08-30 | `523e45393` | Flip the two Int facts + `depends_on` cascade fix (2 files). |
| 2026-08-30 | nat-dist-nth | `Nat.dist` (def + 7 theorems, `nat_prelude/dist.rs`) and `Nat.nth`/`Nat.nthAux` (fuel-bounded, non-mirroring, `nat_prelude/nth.rs`) declared axiom-free; three evaluation-test functions added; kernel-environment-snapshot and refill-headroom regenerated, confirming the screen admits `Mathlib.Data.Nat.Dist` (18) / `Mathlib.Data.Nat.Nth` (11) exactly as ADR-0645 predicted |
| 2026-08-30 | modeq-add-le | Closes `F:ml430-nat-modeq-add-le-of-lt-c774015b` (`Nat.ModEq.add_le_of_lt`) with `Nat.mod_eq_add_le_of_lt`, composing only pre-existing order/monotonicity lemmas — the prior handoff's "2-3 new lemmas" estimate was verified wrong in-tree. `nat_prelude::` sweep 197 -> 198. |
| 2026-08-30 | prime-dvd-mirrors | `bf25ad981` `1fdea582b` `42ccc8e37` -- 13 new theorems (`nat_prelude/prime_dvd_mirrors.rs`) + 1 direct flip to `euclid_lemma`, closing 14/19 dispatchable `ml430` prime-divisibility facts |
| 2026-08-30 | nat-parity-div | 6 new axiom-free Nat kernel theorems (parity/div-two cluster) + 1 mirror flipped onto a pre-existing theorem; 7 of 10 dispatched facts proved, 3 blocked with named reasons |
| 2026-08-30 | fermat-mirrors | `Nat.fermatNumber_ne_one`/`_mono`/`coprime_fermatNumber_fermatNumber` — three new axiom-free kernel theorems (`nat_prelude/fermat_number_mirrors.rs`), facts flipped to `proved` with evidence, 208 `nat_prelude::` tests passing (was 204). |
| 2026-08-30 | pow-add-prime | `Nat.pow_mul`, `Nat.dvd_pow_add_one_of_odd_exp`, `Nat.dvd_pow_add_one_of_odd_mul_exp` — the odd-factor divisibility step toward `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3`, subtraction-free (no alternating sum, no `Int` transport); fact stays `open`, full lemma not assembled |
| 2026-08-30 | `planning` | Accept ADR-0717; add artifact, graph, safety, and discovery roadmaps; promote L0–L4 into the generated primary plan with collision-free 2–3 lane ownership. |
| 2026-08-30 | parity-finish | 3 axiom-free Nat kernel theorems closing the parity/division-by-two cluster's last blockers (`Nat.even_add`, `Nat.even_add'`, `Nat.even_div`); all 3 dispatched facts proved; two of three handoff sizings were wrong (one undersold, one — `even_div` — badly oversold: an existing unconditional lemma closed it in ~75 lines) |
| 2026-08-30 | fermat-easy | 5 axiom-free Nat kernel theorems: the three closed `fermatNumber` reductions (0/1/2 = 3/5/17), `Nat.odd_fermatNumber`, and `Nat.fermatNumber_strictMono`; all fully symbolic except the three closed equalities (largest formed numeral 17) |
| 2026-08-30 | pow-add-prime-finish | `Nat.pow_two_or_has_odd_factor` (odd-factor extraction, ordinary fuel-bounded `Nat.rec`, NOT `WellFounded.fix` — the prior handoff's sizing was wrong) and `Nat.pow_of_pow_add_prime` — closes `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (open → proved, axiom-free); 222/222 `nat_prelude::` |
| 2026-08-30 | l0-s5-kernel-differential | ADR-0717 S5: 32-case kernel differential vs pinned Lean 4.30.0 (0 P0, 1 registered incompleteness), gated in justfile/check.sh, 8-mutation kernel-source kill table (4 killed / 4 survived), ADR-0780 |
| 2026-08-30 | `9b0ba431c` | ADR-0811 and the first `axeyum-machine` A0 word/state/memory/decode/step/run slice. Seventeen direct tests cover every opcode family and branch predicate, exhaustive 8-bit arithmetic flags, modular code wrap, traps, byte order, terminal stuttering, and negative controls. |
| 2026-08-30 | `5e8f4dabb` | `axeyum-machine-evidence` binds the compiled A0 semantic-source digest and emits/recomputes the first finite computation report: all 65,792 8- and 16-bit byte round trips. Reversed byte order and source-digest mutation controls fire with categorized mismatches. |
| 2026-08-30 | `b2b72f777` | Canonical A0 observations and complete dynamic instruction footprints expose selected state, implicit effects, effective memory ranges, and aliased operands. The audit also repaired `halt` incorrectly advancing PC; 19 focused tests now cover the transition and selection controls. |
| 2026-08-30 | `361a733ce` | Semantic package v2 declares the bound A0 surfaces. A trace-class observation artifact recomputes a narrow agreement and broad r3 separation over two complete states; omitting requested r3 fires `semantic-mismatch`. |
| 2026-08-30 | blocked-mirror-divergences | Verified multichoose/minFac divergences against pinned Mathlib source (already resolved by prior lanes, confirmed not re-derived); landed `Nat.testBit_land`/`Nat.testBit_lor` (`F:nat-testbit-land`, `F:nat-testbit-lor`, both axiom-free, transported from the existing `Nat.testBit_xor` technique); wrote ADR-0840 correcting `Nat.fastFib`'s sizing (Mathlib's `fastFibAux` uses a non-dependent `binaryRec` motive, so the existing fuel-based `binaryRec` suffices, but `Nat.fib`'s own divergent construction independently keeps the mirror unflippable regardless) |
| 2026-08-30 | l0-s6-credit-transaction | Crash-safe two-phase-commit engine (`scripts/credit-transaction.py`) + gate (`scripts/check-credit-transaction.py`) + 27-test suite + 9-guard mutation table (`scripts/tests/test-credit-transaction*`), registered in justfile and check.sh; ADR-0785. |
| 2026-08-30 | l1-c0-artifact-contract | Library-artifact pack contract (`artifacts/library-artifact/`: README spec, JSON Schema doc, 9-declaration positive pack + type-only projection + external population registry) + two independent readers (`scripts/check-library-artifact-contract{,-reader-b}.py`) + 14-test suite + 5-guard 1:1 mutation table (`scripts/tests/test-library-artifact-contract*`), registered in justfile and check.sh; ADR-0800. |
| 2026-08-30 | `1ec34c8e1` | Initial module-import parser + receipt generator/checker, verified against the full pinned Mathlib checkout (8,094 modules, 25,495 internal edges, 1,476 sinks, matching the roadmap's evidence baseline exactly); two runs byte-identical. |
| 2026-08-30 | `8e337c9e5` | 12-test suite + 9-mutation harness against a synthetic fixture (all 9 guards kill exactly one test); registered `just module-baseline`/`module-baseline-controls` and three `check.sh` steps. |
| 2026-08-30 | `0e6a1cf15` | L1 phase G2: join the Mathlib declaration graph to ledger facts, kernel declarations, statement vocabulary, destination nodes, producers, declines and trust footprints (ADR-0835). |
| 2026-08-30 | `694f01952` | L2 phase G3: publish the infrastructure frontier -- four frozen queues over the group-defs population, content-hash row ids, seven mutation-verified guards (ADR-0845). |
| 2026-08-30 | 6174be234 | Add `equivalent_to` to `fact.schema.json` and mark all 15 non-canonical duplicate facts with it (surgical text-append edits, `statement`/`formal.statement` untouched); land `scripts/check-proposition-duplication.py` v1 (still failing at 15 unlabeled pairs at this commit, by design -- see report). |
| 2026-08-30 | (this session, later commits) | ADR-0790; `scripts/validate-facts.py` prints the FACTS SETTLED / DISTINCT PROPOSITIONS ESTABLISHED split; `scripts/tests/test-proposition-duplication.sh` (9 cases, 8 guard mutations, each killing exactly one); gate registered in `justfile` and `scripts/check.sh` as `proposition-duplication` / `proposition-duplication-controls`. |
| 2026-08-30 | `847148d3a` | Status doc with root-cause diagnosis (first commit). |
| 2026-08-30 | `2cc851274` | `describe_leak()` + accumulated multi-violation messages; all 11 pre-existing tests pass unchanged. |
| 2026-08-30 | `713ae6b6e` | ADR-0850; `component_split_exemptions` field + validation; exempted the 3 diagnosed crossings in `nursery-v1.json`; gate exit 1 -> 0. |
| 2026-08-30 | `b4f02cd22` | 8 new tests covering detailed messages, multi-violation accumulation, and the exemption mechanism's schema/suppression/self-invalidation. |
| 2026-08-30 | s6-wire-real-ledger | `scripts/credit-transaction-ledger.py` wires ADR-0785's engine into the real write set (fact JSON, pins manifest, safety-matrix) by reusing `validate-facts.py`/`check-settled-fact-statements.py`/`gen-safety-matrix.py` unmodified; gate + 22-test suite + 9-guard mutation table; registered in justfile and check.sh; ADR-0810. |
| 2026-08-29 | nat-rec-agreement | `mod 2 ∈ {0,1}` split + fuel-generalized agreement induction; `bitwise and_fn = land` and `bitwise or_fn = lor` proved universally |
| 2026-08-29 | int-gcd-div | closed `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e` via `declare_exists_mul_mod_eq_gcd`; `Int.gcd_div`/`Int.gcd_div_gcd_div_gcd` re-scoped open with a named blocking lemma gap each, not attempted half-finished |
| 2026-08-29 | nat-bitwise-facts | full triage of all 19 `natural-bitwise` facts; 0 closed (all blocked on out-of-scope files or shared missing machinery, or are mirror mismatches, or a flagged mutation); no source changed |
| 2026-08-29 | int-gcd-div-2 | closed `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc` via `declare_gcd_div_gcd_div_gcd`, an `Int.mul_one`-based finish of the predecessor's Bézout route; confirmed `Int.gcd_div` genuinely absent (no positive-divisor version exists either) and left `F:ml430-int-gcd-div-5e01872f` open with the three missing lemma statements named |
| 2026-08-29 | nat-fuel-irrelevance | Fuel-irrelevance for `landAux` (`Nat.land_aux_eq_land_of_le`), via a new generic two-fuel agreement induction (`agree_by_double_fuel_induction`); transport to `lorAux`/`ldiffAux` sized but not landed; none of the 7 blocked facts closed |
| 2026-08-29 | int-two-sided-induction | `Int.induction_on`: two-sided induction over ℤ, the first combinator in `int_prelude/` that inducts rather than case-splits |
| 2026-08-29 | int-two-sided-induction | `Int.fib_rec`: the Fibonacci recurrence at every integer index, negative ones included |
| 2026-08-29 | int-two-sided-induction | `Int.fib_add` closed (`F:ml430-int-fib-add-181b6a2c` open → proved); it does NOT reduce to `Nat.fib_add` |
| 2026-08-29 | nat-fuel-transport | Transport fuel-irrelevance to `lorAux`/`ldiffAux` (6 new theorems); close `F:ml430-nat-land-comm-7e6ad72e` via a new same-fuel commutativity lemma (`land_aux_comm_of_fuel`) plus the shared-fuel routing (`land_comm`); 6 of 7 blocked facts remain open |
| 2026-08-29 | nat-singles | `Nat.mod_lcm`: unconditional lcm-combination of two congruences, closes `F:ml430-nat-mod-lcm-ee6bdd41` |
| 2026-08-29 | nat-singles | `Nat.dvd_of_forall_prime_mul_dvd`: needs only one prime witness, closes `F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b` |
| 2026-08-29 | nat-singles | `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`) widened `fn` -> `pub(super) fn` so `lcm.rs` can reuse them |
| 2026-08-29 | nat-minfac-relprime | `Nat.IsRelPrime`/`Nat.coprime_iff_isRelPrime`: closes `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` |
| 2026-08-29 | nat-minfac-relprime | `Nat.minFacAux`/`Nat.minFac`: fuel-recursive least-prime-factor definition (bonus; no fact closed, `ml430` mirror stays open — different algorithm from Mathlib's) |
| 2026-08-29 | int-emod-negative | landed `Int.emod_natAbs_bound` (`declare_emod_natabs_bound`, `int_prelude/division.rs`) — the sign-general remainder bound `emod_lt_of_pos` cannot state; `int_prelude::` 40 -> 41 |
| 2026-08-29 | int-emod-negative | landed `Int.ediv_emod_unique_general` (`declare_ediv_emod_unique_general`, same file) — sign-general division-algorithm uniqueness via a negate-and-reduce-to-the-positive-case argument; `int_prelude::` 41 -> 42; `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) left open, precisely scoped to a fourth not-yet-built bridge lemma plus its own mutual-divisibility argument |
| 2026-08-29 | nat-lor-comm | `Nat.lor_aux_comm_of_fuel` (carries `Le m fuel`/`Le n fuel`, unlike `land`'s unconditional analogue) + `Nat.lor_comm`; closes `F:ml430-nat-lor-comm-2666d7ef` via reconciliation with new fact `F:nat-lor-comm`; `bitwise_comm`/`bitwise_swap` sized and left open (need generic-`f` commutativity + the `Nat.bit` decode bridge respectively) |
| 2026-08-29 | nat-testbit-bitwise | Verified all four assigned facts are blocked from an `ml430` flip (codomain mismatch; 3 of 4 additionally by a live gate script); landed `F:nat-zero-of-testbit-eq-zero` as a new local fact (`Nat.testBit_of_zero`, `Nat.sumRange_const_zero`, `Nat.zero_of_testBit_eq_zero`); sized the `testBit_land`/`_lor`/`_ldiff` fuel/index bridge in full detail for the next lane |
| 2026-08-29 | int-fib-two-mul | `eq_sub_of_add_eq_left`, `fib_pred_eq_sub`: the subtraction bridge (a+b=c \|- b=c-a) and its Fibonacci instance (fib(k-1)=fib(k+1)-fib(k)) |
| 2026-08-29 | int-fib-two-mul | `Int.fib_two_mul` closed (`F:ml430-int-fib-two-mul-0e70f3dd` open → proved), no induction, direct algebra from `Int.fib_add`/`Int.fib_rec` |
| 2026-08-29 | int-fib-two-mul | `Int.fib_two_mul_add_two` closed (`F:ml430-int-fib-two-mul-add-two-0ba4a948` open → proved) |
| 2026-08-29 | int-gcd-div | landed `Int.emod_eq_zero_iff_dvd_general` (`declare_emod_eq_zero_iff_dvd_general`, `int_prelude/dvd.rs`) — the sign-general `emod = 0 <-> dvd` bridge the prior lane named but did not build |
| 2026-08-29 | int-gcd-div | closed `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) via `declare_gcd_div` (`int_prelude/gcd.rs`) — mutual-divisibility proof for a divisor of ANY sign or zero, matching Mathlib's unrestricted hypotheses exactly (verified the mirror-flip against Lean 4 core's pinned source, not by name inference); `int_prelude::` 42 -> 47; axiom-free |
| 2026-08-29 | nat-bitwise-assoc | `Nat.land_aux_le_left`/`Nat.land_le_left` (the nested-value bound the assoc brief named); `land_assoc`/`lor_assoc` remain open — precise diagnosis + concrete next-steps recorded above for the next lane |
| 2026-08-29 | ivt-row-two | `CReal.ivt_exact_root_decides_sign` — **ADR-0603 row 2 for IVT**, previously prose in `ivt.rs`'s module doc. An exact root of the plateau family `x ↦ min x (max (x−1) v)` on `[0,1]` yields `Or (le v zero) (le zero v)`; axiom-free, accepted on the first `add_declaration` |
| 2026-08-29 | ivt-row-two | `CReal.ivtPlateau` + `ivtPlateau_nonpos_at_zero` / `_nonneg_at_one` / `_uniformly_continuous` — all three of classical IVT's hypotheses PROVED, so the counterexample family is machine-checked to lie inside its hypothesis class rather than asserted to |
| 2026-08-29 | ivt-row-two | `CReal.uniformly_continuous_max` / `_min` — the lattice's first entries in the closure table `uniformly_continuous_add`/`_neg`/`_sub`/`_mul` fill for the ring. General, modulus `mF n + mG n`, no index shift. `_min` is not `_max`'s dual and the writeup says why |
| 2026-08-29 | ivt-row-two | `F:creal-ivt-exact-root-decides-sign` registered, curated, four discriminating checkers; `validate-facts.py` 1926 facts / 0 errors |
| 2026-08-29 | nat-fastfib-minfac | `Nat.minFacAuxMinimal`/`Nat.min_fac_minimal_of_two_le`/`Nat.coprime_of_lt_min_fac`; new fact `F:nat-coprime-of-lt-minfac`; `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` confirmed staying `open` (not flipped) |
| 2026-08-29 | nat-fastfib-minfac | `F:ml430-nat-fastfib-eq-cde11774` sized and left `open`: needs a new binary/well-founded recursion combinator this prelude does not have yet (not a same-day slice); doubling identities are free from `fib_add(n,n)` once attempted |
| 2026-08-29 | nat-bit-decode | Land the `Nat.bit` decode bridge (`nat_prelude/bit_decode.rs`, new file): artificially-chosen sufficient fuel + `Nat.bit_div_two`/`Nat.bit_mod_two` decode + a `Bool`-first guard-resolution case tree; close `F:ml430-nat-land-bit-b9ab7475` via `Nat.land_bit`. `lor_bit`/`ldiff_bit` remain open — the fuel-swap machinery transports unchanged, but each needs its own per-bit combine agreement lemma (NOT a mechanical transport of `and_cond_mul_eq_cond`; `ble`'s combine needs a further split on `b`) |
| 2026-08-29 | nat-assoc-dichotomy | `Nat.add_eq_zero`/`Nat.zero_or_succ` (the two remaining arithmetic pieces `land_aux_assoc_of_fuel` needs); a fully worked, numerically-verified proof plan showing 6 of 8 base leaves close by pure computation and the hard leaf needs exactly one new theorem (`land_aux_eq_zero_of_left_eq_zero`, fully traced) plus a 3-leaf (not 4- or 8-leaf) top structure; `land_assoc`/`lor_assoc` remain open — `lor_assoc` explicitly flagged as NOT a mechanical transport of this plan |
| 2026-08-29 | nat-xor-parity | Landed `Nat.xor := Nat.bitwise xor_fn` (new `nat_prelude/xor.rs`, reusing `bitwise.rs`'s existing `xor_fn`/`bitwise_xor_three_five` machinery — the same shape Mathlib v4.30 uses) with a discriminating evaluation test (concrete + free-variable); left `F:ml430-nat-even-xor-78a39432`/`F:ml430-nat-lt-xor-cases-c43a1e85` open, reasons recorded (both need machinery — a parity/low-bit bridge, a highest-differing-bit induction — well beyond defining `xor`) |
| 2026-08-29 | nat-parity-lowbit | Landed the parity <-> low-bit bridge (`Nat.even_iff_mod_two_eq_zero`/`Nat.odd_iff_mod_two_eq_one`, new `mod_two_mul_add_of_lt` helper, `nat_prelude/parity.rs`) and `Nat.even_xor` (new `nat_prelude/xor_parity.rs`), closing `F:ml430-nat-even-xor-78a39432` via a new native `F:nat-even-xor`; `F:ml430-nat-lt-xor-cases-c43a1e85` stays open (needs a highest-differing-bit `testBit` induction this technique gives no foothold for) |
| 2026-08-29 | nat-binaryrec | `Nat.Pair` (+`mk`/`rec`/`fst`/`snd`/`fst_mk`/`snd_mk`/`eta`/`ext`) — this prelude's first product type; `Prod` was a test fixture only, confirmed by enumerating every non-test `add_inductive` call site |
| 2026-08-29 | nat-binaryrec | `Nat.binaryRecAux`/`Nat.binaryRec` + 4 refl equations + `binaryRecAux_agree_of_fuel` (double-fuel) + `binaryRec_succ`; new facts `F:nat-binary-rec-fuel-irrelevance`, `F:nat-binary-rec-succ` |
| 2026-08-29 | nat-binaryrec | `Nat.lt_two_mul_of_pos`/`Nat.half_le_of_succ_le_succ` — the halving arithmetic promoted out of four unnamed private copies (`log.rs`, `binary.rs`, `powsq.rs`, `rec_agreement.rs`); the copies are NOT yet deleted |
| 2026-08-29 | nat-binaryrec | `F:ml430-nat-fastfib-eq-cde11774` confirmed staying `open`: Mathlib's `binaryRec` is well-founded recursion with a dependent `Sort u` motive, ours is a non-dependent fuel encoding — a different `def`, so any `fastFib` built here lands as a new local fact. `Nat.fastFib` NOT built. |
| 2026-08-29 | nat-land-assoc-impl | `Nat.land_aux_eq_zero_of_left_eq_zero` (the propagation lemma `252` traced but did not build); a complete, implementation-ready, guard-slot-verified derivation for `land_aux_assoc_of_fuel`'s 4-leaf structure (corrected leaf split order to c,b,a; the hard leaf's double `div_mod_unique` reconstruction closing via `ih` + `mul_assoc` alone, no new lemmas); `land_assoc`'s fuel-bookkeeping shape (mechanical, `land_comm` one slot wider); `land_assoc`/`lor_assoc` remain open |
| 2026-08-29 | nat-lor-ldiff-bit | `Nat.lor_bit` + `Nat.ldiff_bit` (`nat_prelude/bit_decode.rs`): transport the `Nat.bit` decode bridge's fuel-swap machinery unchanged from `land_bit`; new per-operator guard-tree leaves (`lor`'s pass-through rows, `ldiff`'s hybrid) and per-bit combine agreements (`or_cond_max_eq_cond`, `ldiff_cond_eq_cond`). Closes `F:ml430-nat-lor-bit-a2f98c7c` + `F:ml430-nat-ldiff-bit-6be49bb8`, proved axiom-free. Also fixed a pre-existing misplaced `#[test]` attribute in the same test file (unrelated to this lane's subject, needed for a clean clippy gate). |
| 2026-08-29 | nat-bitwise-bit-swap | Land `Nat.bitwise_swap` (`nat_prelude/bitwise.rs`): a fuel-induction cross lemma (`bitwise_aux_swap_of_fuel`) needing NO commutativity hypothesis, since `swap f` beta-reduces to `f` with arguments exchanged; close `F:ml430-nat-bitwise-swap-7175e90e`. Also fixed a pre-existing merge artifact in `nat_prelude_tests.rs` that had silenced `clog_computes_and_its_boundary_equations_apply` as dead code. `bitwise_bit'` remains open. |
| 2026-08-29 | nat-lt-xor-cases | Read the pinned Mathlib v4.30 source for `Nat.lt_xor_cases` directly (no codomain block — fully `Nat`-valued); landed `Nat.xor_comm` (new `nat_prelude/xor_order.rs`, a corollary of `Nat.bitwise_comm` at `f := xor_fn`, one of the pieces Mathlib's own proof route composes) with a discriminating evaluation test; repaired an unrelated pre-existing merge-splice `#[test]`-attribute bug in `nat_prelude_tests.rs` that `cargo clippy -D warnings` exposed; `F:ml430-nat-lt-xor-cases-c43a1e85` stays `open` — precise diagnosis of the 4 remaining substantial pieces (`testBit_xor`, an `exists_most_significant_bit` equivalent, `lt_of_testBit`, `xor_assoc`/`xor_xor_cancel`/`xor_ne_zero_iff`) recorded in `xor_order.rs`'s module doc and this file |
| 2026-08-29 | nat-land-assoc-finish | `Nat.land_aux_assoc_of_fuel`/`Nat.land_assoc` built and kernel-verified, executing `docs/plan/status/257-nat-land-assoc-impl.md`'s traced derivation exactly (leaf split c,b,a confirmed against `guarded`'s guard order; hard leaf's double `div_mod_unique` reconstruction closes via `ih`+`mul_assoc`, no new lemmas); `F:ml430-nat-land-assoc-ad4775b8` closed proved/axiom-free via the standard bitwise reconciliation pattern; a pre-existing merge-splice bug in `nat_prelude_tests.rs` (silently disabling the `clog` test) fixed along the way; `Nat.lor_assoc` characterized but not attempted -- `lorAux`'s pass-through fuel row makes the direct propagation lemma analogue FALSE, not merely harder |
| 2026-08-29 | nat-bitwise-bit-prime | Land `Nat.bitwise_bit'` (`nat_prelude/bitwise.rs`): the generic-`f` counterpart of `bit_decode.rs`'s `land_bit`/`lor_bit`/`ldiff_bit`, needing a new `Bool`-round-trip lemma (`cond_beq_one_eq_self`) for the per-bit combine and a new "generalize with equality" case-split (`cases_zero_succ_with_eq`) to discharge the two side hypotheses that close a leading-zero ambiguity the fixed-`f` specializations never have. Kernel accepted on the first attempt. Closes `F:ml430-nat-bitwise-bit-4c4b28a8`, proved axiom-free -- all four `Nat.bit`-decode `*_bit` facts are now closed. |
| 2026-08-29 | nat-testbit-xor | Landed `Nat.testBit_xor` (new `nat_prelude/testbit_bitwise.rs`), bridging `testBitAux`'s index recursion with `bitwiseAux`'s value recursion via an induction on the bit index generalized over both operands, reduced to two new per-step lemmas (`xor_low_bit`, `xor_div_two`) that reuse `xor_parity.rs`'s one-step-unfold technique and `bitwise.rs`'s fuel-irrelevance machinery; admitted by the trusted kernel gate on the first attempt, axiom-free; registered as a new local fact `F:nat-testbit-xor` (codomain mismatch with Mathlib's `Bool`-valued `testBit` rules out an `ml430` mirror flip); piece (1) of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`, which stays `open` — pieces 2-4 unchanged from `docs/plan/status/260-nat-lt-xor-cases.md` |
| 2026-08-29 | nat-xor-algebra | Landed `Nat.eq_of_testBit_eq` (new general "same bits imply the same number" extensionality lemma, generalizing `Nat.zero_of_testBit_eq_zero`) and `Nat.xor_assoc` (via `Nat.testBit_xor` applied twice per side plus the new extensionality lemma, using a from-scratch `xor_bit` Boolean-algebra toolkit — `digitize`/`cases_bool`/`beq_digitize_one`/`bool_xor_assoc`/`congr_bool_to_nat`/`xor_bit_assoc` — confirmed by Python truth-table simulation before any Rust; a real `TypeMismatch` bug was isolated via a throwaway probe module rather than by reading a poisoned 147-test failure list), new file `nat_prelude/xor_algebra.rs`, both axiom-free with concrete+symbolic evidence, both new local facts (no `ml430` mirrors: read directly at the pinned Mathlib commit, `xor_assoc`/`xor_xor_cancel`/`xor_ne_zero_iff` are Lean4 core lemmas cited but not defined in `Bitwise.lean`); `F:ml430-nat-lt-xor-cases-c43a1e85` stays `open` — `Nat.xor_xor_cancel_left`/`_right` and `Nat.xor_ne_zero_iff` remain, with an exact diagnosed route through a `y ∈ {0,1}` round-trip lemma this lane discovered is needed (the natural "cancel" identity is FALSE for general `y : Nat`, unlike `xor_assoc`'s identity which stays at the `digitize`/`Bool` level throughout) |
| 2026-08-29 | nat-msb-order | Landed `Nat.self_lt_two_pow`/`Nat.self_lt_two_pow_add` (new general arithmetic toolkit, `nat_prelude/bit_order.rs`) and `Nat.lt_of_testBit` (piece 3 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`, registered as the new local fact `F:nat-lt-of-testbit` since Mathlib's `testBit` is `Bool`-valued and this kernel's is `Nat`-valued), admitted axiom-free on the first real kernel-check attempt via a `sumRange_split`-based decomposition around a common bound `N := add n (add m (succ i))`; piece 2 (`exists_most_significant_bit`) diagnosed but NOT landed -- its "zero above the top bit" half has a specified cheap route (reusing this lane's own bound-construction technique), its "highest bit really is set" half remains a full lane needing a new `size`-recursion lemma or an independent bottom-up construction |
| 2026-08-29 | nat-lor-assoc | `Nat.lor_aux_ne_zero_of_right_ne_zero` — the invariant that replaces "zero propagates" for `lor_assoc`'s hard leaf, kernel-verified and tested (land's direct analogue is FALSE for `lor`, confirmed numerically before any Rust: `lor a b = 0` forces `a=b=0`, so `lor a (lor b c)` collapses to `c`, not `0`); a complete, numerically-cross-checked derivation for the rest of `lor_assoc` (the full `lor_aux_assoc_of_fuel` case tree — SIMPLER than `land`'s hard leaf once this invariant exists, since `X`/`Y` are unconditionally positive rather than needing a real zero/nonzero dichotomy — plus the one remaining new lemma `lor_bit_assoc` and the refuel bound `lor_aux_le_add`, both fully specified); `F:ml430-nat-lor-assoc-82c4d0fd` remains open |
| 2026-08-29 | nat-lor-assoc-exec | Closed `F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) via new native `F:nat-lor-assoc` -- executed `docs/plan/status/266-nat-lor-assoc.md`'s full trace (`lor_bit_assoc`, `lor_aux_assoc_of_fuel`, `lor_aux_le_add`, `lor_assoc`) verbatim; every traced step held, including `lor_aux_le_add`, the one piece the tracing lane had not sub-step-verified in Python. One transcription bug (a `y_succ_case` closure closing over the wrong dichotomy's binders) found and fixed by self-review before the first compile; kernel accepted on the first check thereafter. `nat_prelude::` 152 -> 153 tests, axiom-free, `the_build_is_deterministic` pin `93+505 -> 93+508` |
| 2026-08-29 | nat-xor-cancel | Landed `Nat.xor_xor_cancel_left` (via `Nat.testBit_xor` + a new per-bit cancel lemma needing a new `y <= 1` round-trip lemma the natural identity does not hold without, since it is FALSE for general `y : Nat`) and `Nat.xor_xor_cancel_right` (transported from `_left` via `Nat.xor_comm` twice, no new per-bit argument); both axiom-free with concrete+symbolic evidence, both new local facts (no `ml430` mirrors, same reasoning as `F:nat-xor-assoc`); a mislabeled chain intermediate in the theorem-level wiring found via a throwaway bisecting probe rather than by reading a 152-test poisoned failure list; `F:ml430-nat-lt-xor-cases-c43a1e85` stays `open` — only `Nat.xor_ne_zero_iff` remains of piece 4's four sub-targets, and its forward direction does NOT need the cancel lemmas (a direct corollary of `Nat.eq_of_testBit_eq` + `Nat.testBit_xor` + the same `{0,1}` case-split shape), while its reverse direction and `Iff` packaging were not attempted |
| 2026-08-29 | nat-msb-exists | Landed `Nat.testBit_eq_zero_of_lt` (the "cheap half" of `exists_most_significant_bit`, piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`) as the new local fact `F:nat-testbit-eq-zero-of-lt` (Mathlib's `Nat.testBit_eq_false_of_lt` is Bool-valued; ours stays Nat-valued), admitted axiom-free on the first real kernel-check attempt via `value_eq_sum_range` at `bound := j` and `bound := succ j` plus `sum_range_succ`/`add_left_cancel`/`mul_eq_zero`; the "highest bit is set" hard half remains open and is re-confirmed (not newly discovered) to need either a new `size`-recursion lemma relating `size n` to `size (n/2)` or an independent ~150-line bottom-up `msbAux`-fuel construction |
| 2026-08-29 | nat-xor-ne-zero | Landed `Nat.xor_ne_zero_iff` (piece 4's fourth and last sub-target toward `F:ml430-nat-lt-xor-cases-c43a1e85`), read directly from the pinned Batteries checkout (`Batteries/Data/Nat/Bitwise/Lemmas.lean:68`, confirming the "Lean core, not Mathlib" reading two prior lanes established for its siblings); built via `mt` (modus tollens, previously declared but unused in this prelude) applied twice rather than an `Iff`-of-`Eq` intermediate; the `mpr` direction confirmed NOT needing the cancel lemmas per the prior lane's own handoff, via a new per-bit lemma reusing `round_trip_le_one`; the `mp` direction via a new `Nat.xor_self`-shaped argument; every route confirmed by Python truth-table simulation before writing Rust, and no `false_true_elim` needed anywhere; new fact `F:nat-xor-ne-zero-iff`, axiom-free; all four of piece 4's sub-targets now landed, leaving 2 of the original 4 larger pieces (`lt_of_testBit`, `xor_trichotomy` composition) plus `lt_xor_cases` itself |
| 2026-08-29 | nat-msb-hard | Landed `Nat.msb_exists_of_le_fuel` (fuel-generalized) and `Nat.exists_most_significant_bit` (the hard half of piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`: the highest bit really IS set, not just that no higher bit is needed) as the new local fact `F:nat-exists-most-significant-bit` (Mathlib's `testBit` is Bool-valued; ours stays Nat-valued), admitted axiom-free on the first real kernel-check attempt via an independent fuel/half-recursion (same `div_mod_lt_mul_iff`+`n_lt_mul_two` bound `declare_size_aux_lt_pow` uses, split on `beq half zero` mirroring Mathlib's `Nat.binaryRec`) rather than a `size`-recursion lemma -- `Nat.size` re-confirmed to not shortcut this, since its own development only ever proves an upper bound; pieces 1-3 of the 4 pieces blocking `lt_xor_cases` are now all DONE, piece 4's status needs a fresh check before dispatching the final composition |
| 2026-08-29 | nat-lt-xor-cases-final | Closed `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`) by composing the four pieces five prior lanes landed the same day (`testBit_xor`, `exists_most_significant_bit`, `lt_of_testBit`, `xor_assoc`/`xor_xor_cancel_left`/`_right`/`xor_ne_zero_iff`) via an auxiliary `Nat.xor_trichotomy` theorem following Mathlib's own proof route (read directly from the pinned v4.30 source, `Mathlib/Data/Nat/Bitwise.lean:266-297`); both admitted axiom-free on the first real kernel-check attempt (new file `nat_prelude/xor_trichotomy.rs`); the fact is fully `Nat`-valued so the flip is honest, unlike six sibling `testBit`-family mirrors this session found unflippable; `xor_xor_cancel_right` turned out unnecessary for the rotation identities, contra Mathlib's own tactic proof which uses it once |
| 2026-08-29 | logic-excluded-middle | `Formula` AST + 3-element Heyting-chain semantic countermodel (`ipc_heyting.rs`); new fact `F:heyting-3-chain-refutes-excluded-middle` (proved); `F:excluded-middle-not-intuitionistic` stays open with scoping notes recorded |
| 2026-08-29 | `a94927553` | `F:cas-extremum-deriv-sign-bracket-kernel-checked` — new bridge file `rat_prelude/cas_extremum_deriv_bridge_tests.rs`; kernel-reconstructed 4→5 |
| 2026-08-29 | `d57773ad2` | `F:cas-mvt-secant-endpoints-kernel-checked` — new bridge file `rat_prelude/cas_mvt_secant_bridge_tests.rs`; kernel-reconstructed 5→6 |
| 2026-08-29 | `af6d9f1e6` | `F:cas-taylor-remainder-lhs-kernel-checked` — new bridge file `rat_prelude/cas_taylor_remainder_bridge_tests.rs`; kernel-reconstructed 6→7 |
| 2026-08-29 | (see commits above) | `artifacts/kernel-stack-envelope.tsv`: `integer`/`cpoint`/`complex` release rows raised to their measured minimums (131,072 / 8,388,608 / 8,388,608); `complex` debug row raised to 16,777,216; `integer`/`cpoint` debug rows confirmed unchanged. Growth attributed per-prelude to that prelude's own recent commits (int gcd/fib lemmas, cpoint's squared-throughout geometry identities, complex's polynomial/factor-theorem family), refuting a uniform-nat-growth hypothesis. `nat`/`rat`/`creal`'s sub-2x-margin rows deliberately left unraised (passing, out of scope, owned by other lanes). |
| 2026-08-29 | `94292a1fb` | arity survey of the 10 geometry certificates; fixed-arity alternative refuted for geometry (arities 6–19); varignon and thales identified as carrying vacuous identities |
| 2026-08-29 | `1cd4aa0ab` | `rat_prelude/cas_geometry_bridge_tests.rs` — the multivariate bridge: representation choice, `prove_scale`/`prove_merge`, translator tests green |
| 2026-08-29 | (this commit) | `F:geometry-orthocentre-cofactor-identity-kernel-checked` — the first multivariate CAS→kernel reconstruction, symbolic in 8 variables, axiom-free, mutation-verified both halves; cas-certificate kernel-reconstructed 7 → 8 |
| 2026-08-29 | `237c1abdd` | Re-derive 1054 missing `depends_on` edges across 306 facts; `check-fact-depends-derived.py` was genuinely stale (182 commits since last fix), not broken. |
| 2026-08-29 | `166e789d1` | Repair the premise-selection proved-prefix control's stale fixture (the chain it mutated is now genuinely all-`proved`); guard itself confirmed sound by delete-and-recount. |
| 2026-08-29 | `2bd5d391c` | Fix `check-control-tests-reachable.py`'s false-credit bug: `control-optout.tsv`'s bare (non-`#`) exclusion rows were vouching for modules they name as unrun. `ORPHAN_BASELINE` 14 -> 16 (corrected measurement, not new rot). |
| 2026-08-29 | `0348564ab` | Break the `auto<->nat_induction` and `qinst_egraph<->quant_instance_set_cert` cycle-closing edges from 2026-08-17; `modules_in_cycles` now matches the pre-regression baseline exactly. Residual mass/fan-out growth on the same gate is pre-existing, tracked by D1/D3, left untouched. |
| 2026-08-29 | int-parity-two | 7 of 10 `ml430` division-by-two mirrors closed (`Int.emod_two_ne_zero`/`_ne_one`, `Int.ediv_two_mul_two_of_even`, `Int.ediv_two_mul_two_add_one_of_odd`, `Int.add_one_ediv_two_mul_two_of_odd`, `Int.odd_of_mul_left`/`_right`), all axiom-free; `even_add`/`even_add'`/`even_add_one` left open |
| 2026-08-29 | nat-div-mod-family | `Nat.add_mul_div_left`/`_right`, `Nat.add_mul_mod_self_left`/`_right`, `Nat.add_mod_left`/`_right`, `Nat.add_div_left`/`_right` — 8 of 9 dispatched `ml430` add/div/mod mirrors, axiom-free, via a new reusable `div_mod_shift` helper (`nat_prelude/div_mod_lemmas.rs`). `add_div_of_dvd_add_add_one` left open (needs a different argument). |
| 2026-08-29 | `04a77fbf6` | example-inventory count regenerated 193 -> 202 (real growth). |
| 2026-08-29 | `dcc100cc6` | PLAN.md regenerated for the same count. |
| 2026-08-29 | `e72119787` | lane-turn-controls case 4 fixture fixed: SKIP a stale baseline instead of asserting a false expectation. |
| 2026-08-29 | nat-lcm-gcd | `Nat.gcd_dvd_mul`, `Nat.gcd_le_mul`, `Nat.eq_zero_of_lcm_eq_zero`, `Nat.lcm_assoc`, `Nat.lcm_div` — 5 new axiom-free theorems (`nat_prelude/lcm_gcd_lemmas.rs`), plus 5 status-flip closures of pre-existing `Nat.lcm_comm`/`Nat.lcm_dvd`/`Nat.dvd_lcm_left`/`Nat.dvd_lcm_right`/`Nat.gcd_mul_lcm`. 10 of 10 dispatched `ml430` lcm/gcd mirrors closed. |
| 2026-08-29 | nat-totient | `Nat.coprime_succ_self` (new: consecutive naturals are coprime) and `Nat.totient_eq_zero` — 1 of 9 dispatched `ml430` totient mirrors, axiom-free, via a top-index-witness argument (`nat_prelude/totient_lemmas.rs`). The other 8 triaged and left open: blocked on a general existence-witness-to-positive-count lemma and/or the `totient_even` fixed-point-free-involution pairing argument and/or the multiplicative formula for `totient` — none built yet, none a small addition. |
| 2026-08-29 | int-emod-additive | `emod` additive law (`Int.ModEq`-based `modeq_add`) + `Int.even_add`/`Int.even_add'`/`Int.even_add_one` closed, all axiom-free; two `nat-*` stragglers left for a future lane |
| 2026-08-29 | depends-producer | `check-fact-depends-derived.py --fix` mode: derives, surgically patches, and self-verifies `depends_on` edges; wired into `validate-facts.py` as the landing-time gate (`--skip-depends-derived` escape hatch); 21 new mutation-controlled tests. |
| 2026-08-29 | totient-counting | `Nat.countRange_succ_of_true`, `Nat.countRange_le_of_le`, `Nat.countRange_ge_two_of_two_witnesses` — the general "two distinct witnesses ⇒ count ≥ 2" machinery (piece 1 of the nat-totient triage), axiom-free, chosen over the `Int.prod_range_pairing_collapse`-transport route (checked, does not corollary) and the multiplicative-formula piece because it needed no new induction. Does not close any mirror by itself; the exact remaining trichotomy assembly for `totient_eq_one_iff`/`dvd_two_of_totient_le_one` is recorded in `totient_lemmas.rs`'s module doc for the next lane. |
| 2026-08-29 | nat-stragglers | `Nat.add_div_of_dvd_add_add_one` — the ninth/last `ml430` add/div/mod shift-family mirror, axiom-free (new file `nat_prelude/div_mod_lemmas.rs` extension). |
| 2026-08-29 | nat-stragglers | `Nat.base_induction` — strong induction over `Nat.lt`'s well-foundedness, axiom-free (new file `nat_prelude/base_induction.rs`); confirmed the pinned source is Lean core (`Init.Data.Nat.Div.Lemmas`), not Mathlib proper. |
| 2026-08-29 | `2f9162c98` | Five `Nat` mul/div order mirrors (`mul_lt_mul_left`/`right`, `lt_of_mul_lt_mul_left`/`right`, `div_lt_of_lt_mul`) in a new `nat_prelude/mul_order_lemmas.rs`; five facts flipped to `proved`. |
| 2026-08-29 | nat-mod-mul | `0f07031a6` new `nat_prelude/mod_mul_lemmas.rs`: `mod_mul`, `mod_mul_left_mod`, `mod_mul_right_mod`, `mod_mul_left_div_self`, `mod_mul_right_div_self`, kernel type-checked. |
| 2026-08-29 | nat-mod-mul | `99c59c0c1` register the five names in `theorem_names`, bump `the_build_is_deterministic`'s pin 93+538 -> 93+543, fix rustfmt mod/use order, fix a clippy too-many-arguments miss. `cargo test --lib nat_prelude::` 169 passed. |
| 2026-08-29 | nat-mod-mul | `46ddfaf3e` flip all five `F:ml430-nat-mod-mul-*` facts to `proved` with kernel-term + axiom-footprint evidence; `validate-facts.py` 0 errors. |
| 2026-08-29 | totient-multiplicative | `Nat.coprime_div_left` (1 of the family's remaining mirrors, closed) and `Nat.gcd_comm` (new, zero-induction, unblocks both this family's `totient_even` plan and the multiplicative-formula plan below) landed and verified. The multiplicative formula `totient(mn) = totient(m)*totient(n)` itself: fully traced and numerically checked (bijection, mod-gcd invariance, pointwise coprimality iff, Bézout-multiplication algebra, the row-major double-counting target statement), with the two genuinely novel pieces identified and marked (`coprime_mul_of_coprime`, the coprimality-combine number theory; `count_range_row_major`, the totient-independent double-counting induction) — NOT built in Rust, per this task's own sizing guidance. `nat_prelude/crt.rs` (Nat-native, not the `int_prelude` one) was found to transport directly for the injectivity/pigeonhole half, correcting all three prior triages, which did not find it. |
| 2026-08-29 | int-add-basics | Nine `ml430-int-add-*` mirrors closed: `add_comm`/`add_neg_cancel_right` already existed (evidence only); `add_left_neg`/`add_neg_eq_sub`/`add_left_comm`/`add_mul`/`add_neg_cancel_left`/`add_left_cancel`/`add_left_inj` newly built in `int_prelude/add_basics.rs`, all axiom-free, no `Int.rec` case split. |
| 2026-08-29 | orphan-script-audit | `98d17aeef` census + archive 346 dead `check-autogenesis-*` scripts (+ 92 controls) to `scripts/archive/`; register `check-shared-index.sh`, `check-sos-negative-controls.sh`, `check-evidence-portability.sh` as new gate steps |
| 2026-08-29 | orphan-script-audit | `810ef0807` fix 3 `scripts/control-optout.tsv` entries left stale by the archival; lower `OPTOUT_CEILING` 18 -> 15 |
| 2026-08-29 | `203712454` | step 0 re-measurement: the "8 more geometry certificates" sizing corrected to 3; `parallelogram-diagonals-bisect` needs the fractional cast too |
| 2026-08-29 | `e253e79cd` | `rat_prelude/cas_geometry_mul_bridge_tests.rs` — `prove_mul`: monomials as sorted factor lists, three layers, `one_mul`/`zero_mul` derived |
| 2026-08-29 | `f24f87fa9` | `Check.geometry_rhombus_cofactor_identity` admitted — 9 variables, 4 polynomial cofactors, axiom-free; rewrite directions recovered from the parent module's call sites |
| 2026-08-29 | `4b9d63e9e` | `F:geometry-rhombus-cofactor-identity-kernel-checked` registered; cas-certificate kernel-reconstructed 8 → 9; mutation-verified both halves |
| 2026-08-28 | pi-rung3 | `CReal.sinFnLowerBoundOneToR` -- pi rung 3: a uniform lower bound `sin z >= 1/4` on `[1, 8/5]`, kernel-accepted (`existing_step_order_is_topologically_valid`, ~97-99s). Five kernel rejections fixed: an empty-context `infer` on an open term, two `Int`/`Nat` argument mixups in `normalize_mul_normalize` calls, a `rat_eq_rewrite` anchor typed wrong, `NatOps`'s `Nat`-hardcoded transport misused on a `CReal` value (new `creal_transport`/`creal_eq_motive` fix it), and a ι-defeq assumption between a succ-chain exponent and `Nat.succ_add`'s own target that does not hold without the propositional bridge |
| 2026-08-28 | pi-rung3 | measured: `alternatingLowerBound`'s internal `t_lam` (RIGHT-associated `sign*(coeff*pow)`) is Equiv but never defeq to `CReal.sinFnTerm` (LEFT-associated `(sign*coeff)*pow`) -- the largest of the five rejections. Fixed by building the whole domination/Converges/squeeze chain around `t_lam` directly (`build_t_lam_here`, interning-identical to `alternating.rs`'s own private `build_t_lam`) and bridging to `sinFnTerm` only at the two points that need it (`dom_hyp`, and the squeeze's `sinFnUniformConverges`-derived leg), the second via a per-fixed-`n` `sum_range_congr` equiv rather than any uniform-in-`n` `Converges` transport |
| 2026-08-28 | pi-rung3 | verified before building: 169-pi.md's own arithmetic (`119/375 >= 1/4` via `119*4=476>=375`, antitonicity `z^2<=64/25<=6<=(2k+2)(2k+3)`, `k:=3`) checks out exactly; largest cross-product actually needed (`64*8=512`, sum-check denominator `3000`) stayed comfortably under the 10^3 estimate |
| 2026-08-28 | pi-r2b | `CReal.cosWideTailNonneg` -- `forall k, le zero (mul (expTerm (add k k)) (pow R (add k k)))`, `R := 8/5`. Direct from `mul_nonneg`/`exp_term_nonneg`/`pow_nonneg`. Accepted first try |
| 2026-08-28 | pi-r2b | `CReal.cosWideTailAntitone` -- the sized `htail` blocker, `forall k, le (a (succ (succ k))) (a (succ k))` for cosine's magnitude sequence at `R := 8/5`. Reduces to `R^2 <= (m+1)(m+2)` at `m := add(succ k)(succ k) >= 2`, closed via TWO applications of the already-landed `CReal.expTermSuccScale` plus a small `Rat.ble`-computed numeric fact (`64/25 <= 3`) rather than hand-rolled cross-multiplication. Accepted first try, axiom-free |
| 2026-08-28 | pi-r2b | technique: a SMALL concrete `Rat.le` fact (`R^2 <= 3` here) is cheaper via `Rat.ble`'s own computation (`Eq.refl` at `Bool.true` after the kernel reduces `Rat.ble a b` on small literal numerals) than a hand-rolled `Rat.normalize_cross`/`int_le_of_mul_le_mul_right` battery -- reusable for item 4's numeric leaf |
| 2026-08-28 | pi-r2b | measured NEGATIVE, read not guessed: `docs/plan/status/174-pi-rung2.md`'s item 3 ("mechanical given `htail`") understates the remaining gap. Bridging `cosFnWideUniformConverges`'s `close_within`-shaped `.spec` output down to `Converges`'s own `Within`-on-rationals-at-a-shared-index shape needs (a) `close_within` -> two one-sided `le`s, (b) `CReal.within_of_two_sided_le` (the only general "real inequality -> Within" bridge in the tree) to reach a real-indexed `Within`, and (c) a `CReal.add`-index-shift regularity bridge of the same kind `CReal.converges_add`'s own doc names as its hardest step -- confirmed absent by reading `convergence.rs`, `order_extra.rs`, and every `close_within`-mentioning file in `creal/` |
| 2026-08-28 | pi-r2b | `le (cosFnWide R) zero` itself did NOT land; items 3 and 4 remain open for the next lane, with item 3 now sized as a `converges_add`-sized bridge rather than "mechanical" |
| 2026-08-28 | pi-r2b | measured: the kernel rejected NOTHING -- both `add_declaration` calls succeeded first attempt, no `on_a_deep_stack` needed. `creal_prelude_builds` 94.45 s (inside the 91-117 s band, no measurable slowdown); `every_creal_declaration_is_checked_and_axiom_free` green in `--release` (15.09 s), both declarations `Theorem`-kind, empty `axiom_footprint` |
| 2026-08-28 | cw-bridge | `CReal.converges_of_abs_diff_le` — `close_within` evidence → `Converges`, axiom-free, first-attempt accept |
| 2026-08-28 | cw-bridge | the shift bridge it was sized to need already existed: `CReal.sharedIndexToCanonical` (`integral.rs`) + `cauchy_of_abs_diff_le` (`ivt.rs`) |
| 2026-08-28 | `68e0a48d8` | dedup: cite `CReal.abs_add_le` instead of re-deriving it, in 4 `creal/` files; fix a stale "does not exist" doc comment |
| 2026-08-28 | rs-cauchy | no code change — `riemannSum_cauchy`/`CReal.integral` roadmap through `integral_by_parts` confirmed already landed and axiom-free; re-verified `creal_prelude_builds` (96.79s) and environment-derived coverage check (14.92s, `--release`) |
| 2026-08-28 | pi-r2d | `crates/axeyum-lean-kernel/src/creal/cos_sign.rs`: re-added `CReal.cosWideSeriesConverges` (item 3, unchanged from the reverted `pi-r2c` attempt) and rewrote `CReal.cosWideNonpositive` (item 4) to collapse each series term to a flat, already-reduced `Rat` literal (`collapse_to_flat`/`small_rat`) BEFORE combining via `Rat.add`, instead of nesting three un-reduced `Rat.mul`/`Rat.pow`/`Rat.normalize` towers as the reverted attempt did. `cargo check`/clippy green. `creal_prelude_builds` NOT observed to finish by this lane — do not treat either theorem as landed on the strength of this row alone |
| 2026-08-28 | pi-r2d | measured (hand-traced, not kernel-timed): the reverted attempt's own final numeric check never needs a `Nat` value above `25*1875=46,875` if combined in `sumRange`'s forced left-nested order — under the documented `60,000`-feasible line — which is evidence the 616s/5.9GB blowup was driven by NESTING DEPTH of un-reduced `Rat` towers rather than by final operand magnitude alone. Offered as a hypothesis, not a confirmed measurement; no isolated A/B was run to separate the two causes |
| 2026-08-28 | pi-r2d | negative, precise: the brief's "rescale every term to an explicit denominator-1875 `Rat` value" is impossible as literally stated — `Rat`'s `reduced` field (`gcd(|num|,den)=1`) rules out constructing `1875/1875` or `-2400/1875` as `Rat.mk` terms at all. Implemented instead: each term collapses to its own naturally-reduced flat value, combined via ordinary `Rat.add` at bounded (~46,875) scale |
| 2026-08-28 | pi-r2d | item 4 REVERTED twice; two independent constructions both exceed the build band, so the `Rat.ble` route does not reach `-13/1875` |
| 2026-08-28 | pi-r2e | `crates/axeyum-lean-kernel/src/creal/cos_sign.rs`: **π rung 2 complete.** `CReal.cosWideSeriesConverges` (item 3) and `CReal.cosWideNonpositive : le (cosFnWide R) zero` (item 4) both admitted and axiom-free; `creal_prelude_builds` 100.65 s baseline → 113.46 s, in the 94–123 s band, personally observed |
| 2026-08-28 | pi-r2e | measured: item 3 costs **+0.6 s** (100.65 → 101.22), isolated for the first time. Both reverts were paying for item 4 alone |
| 2026-08-28 | pi-r2e | measured, and it settles the two open attributions: `NatOps::num` builds a **unary** numeral and `tc.rs::reduce_nat_binop`'s acceleration needs a `Lit::Nat`, which `reduce_nat_succ` never produces from `succ (Const Nat.zero)` — so **no `Nat` arithmetic in this prelude accelerates** and cost is superlinear in the largest magnitude formed. Not "operand size" and not "nesting depth" on their own |
| 2026-08-28 | pi-r2e | measured A/B on the SAME method: bounding `t 2` at `8/75 ≤ 7/64` (largest `Nat` 525) rather than at the exact `512/1875 ≤ 7/25` (13,125) is **587.02 s → 113.46 s**. Both constructions were accepted by the kernel; the first was correct and 5.8× too slow |
| 2026-08-28 | pi-r2e | negative, precise: `Rat.neg_nonpos_of_nonneg` and the `Rat.nonneg_of_int_nonneg` numerator bridge both already exist, and neither helps — the cost was forming `-13/1875`, never comparing it to zero. The value is now never built at all |
| 2026-08-28 | pi-r2e | process: a `cargo test` timing under lane contention measures the `cargo-serialized.sh` flock queue, not the kernel; one run hit the 600 s wall that way. Long kernel readings must come from `target/debug/deps/axeyum_lean_kernel-*` run directly |
| 2026-08-28 | supon-r6 | `supOn` rung 6: the multi-level nearest-mesh-point lemma, the `eps`/existential transport combinator, and the arbitrary-depth gap bound — three first-attempt kernel accepts, axiom-free |
| 2026-08-28 | choose-backlog | 5 Nat.choose theorems (one_right, eq_zero_of_lt, ne_zero, le_succ, symm_of_eq_add) + 5 facts flipped to proved; fixed a false defeq assumption in choose_le_succ's base case |
| 2026-08-28 | coprime-backlog | 4/5 `Nat.Coprime` import-backlog facts proved axiom-free (`coprime_of_dvd_left/right`, `prime_dvd_iff_not_coprime`, `coprime_add_self_right`); `coprime_two_left` deferred, needs a fresh `Odd` construction |
| 2026-08-28 | decidable-frontier | confirmed F:rado-r4-a5-b3 and F:rado-r4-a5-b4 already settled, no edit made; added a corroborating 2026-08-28 re-measurement to F:fp16-add-monotone-rne's notes (drat_check throughput ~95 steps/s, ~2.4h extrapolated), fact stays `open` |
| 2026-08-28 | evt-r2-gap | Closed EVT row-2's labeled gap: promoted `abs_bound_of_self`, added `bounded_on_id_zero_one` and `evtLinear_uniformly_continuous` (all kernel-checked) |
| 2026-08-28 | drat-evidence-route | `certify_unsat_via_lrat`: the backward engine emits LRAT hints (untrusted), `check_lrat` verifies them (trusted, search-free) — fp8 evidence 25m46s -> 5.0 s and fp16 never-finished -> 125 s, with no move of the trusted base (ADR-0613) |
| 2026-08-28 | nat-cascade | `Nat.choose_le_add`, `Nat.choose_symm_add` proved (`nat_prelude/choose.rs`); pinned `65+331`->`65+333` in `the_build_is_deterministic` |
| 2026-08-28 | nat-cascade | `Nat.coprime_of_dvd`, `Nat.coprime_self_add_right`, `Nat.coprime_symmetric`, `Nat.coprime_or_dvd_of_prime` proved (`nat_prelude/primes.rs`); pinned `65+333`->`65+337` |
| 2026-08-28 | `de8d37ef5` | `Nat.Even`/`Nat.Odd` + `even_or_odd_exists`, `add_self_ne_succ_add_self`, `even_not_odd`, `odd_not_even`, `even_iff_odd_succ` (new `nat_prelude/parity.rs`) |
| 2026-08-28 | `acc299135` | register the 7 new declarations in `every_nat_declaration_is_checked_and_axiom_free`'s inventory; recount `the_build_is_deterministic`'s pin (65+331 -> 67+336) |
| 2026-08-28 | `4cf8aa9ec` | concrete-witness cross-check (`Even 4`, `Odd 5` hand-built) catching an `mp`/`mpr` swap that type-shape alone would not |
| 2026-08-28 | int-modeq | `Int.ModEq.add_left`/`add_right` generalized to drop `0<n` (Mathlib parity); five new unconditional facts (`add_left_cancel`, `neg`, `neg_modEq_neg`, `of_dvd`, `dvd_iff`, `of_mul_left`) landed via two new helpers `modeq_to_dvd`/`dvd_to_modeq`; all seven backlog facts flipped `open`→`proved`, axiom-free |
| 2026-08-28 | parity-coprime | `Nat.choose_le_choose` proved (`nat_prelude/choose.rs`); pinned `67+342`->`67+343` in `the_build_is_deterministic` |
| 2026-08-28 | parity-coprime | `Nat.coprime_of_lt_prime` fact flipped to proved (already admitted pre-existing kernel declaration, no new Rust) |
| 2026-08-28 | parity-coprime | `Nat.coprime_two_left`, `Nat.coprime_two_right`, `Nat.Coprime.odd_of_left`, `Nat.Coprime.odd_of_right` proved (`nat_prelude/primes.rs`); pinned `67+343`->`67+347` |
| 2026-08-28 | supon-r6b | what landed, in one line |
| 2026-08-28 | nat-numeral-accel | `NatOps::num` → `Lit::Nat`: `reduce_nat_binop` now reachable (1.6M× on `gcd 512 1875`), no proof edited, prelude-build win measured at ~zero, and 12 pins + 3 scripts + 5 fact checkers + 388 fact statements move on rendering (ADR-0613, proposed) |
| 2026-08-28 | main-red-tests | `qfbv-proof-export` could not succeed on ANY input since `81361cdd1` made `set-logic` positional; and the `creal` prelude outgrew the 2 MiB default stack (16 MiB debug / 8 MiB release measured, pinned at 2 MiB / 128 KiB) so every constructed-reals test aborted the binary |
| 2026-08-28 | fp16-evidence | `F:fp16-add-monotone-rne` flipped open -> proved; attached `unsat-certificate` evidence row with discriminating `checker_command` (ADR-0613 LRAT route), reproduced end-to-end twice (339s, 353s wall clock) |
| 2026-08-28 | int-gcd | `Int.ne_zero_of_gcd` + `Int.gcd_eq_one_of_gcd_mul_right_eq_one_left`/`_right` landed as new kernel declarations in `int_prelude/gcd.rs`; three ml430 facts flipped `open`→`proved`, axiom-free; `Int.gcd_eq_gcd_ab` (existential Bézout) confirmed NOT the same fact as Mathlib's computable `gcd_eq_gcd_ab` and left open with a sized reason; `gcd_div`/`gcd_div_gcd_div_gcd`/`gcd_greatest` not attempted |
| 2026-08-28 | nat-helper-dedup | promoted `two_divisor_dichotomy` (3→1), `two_mul_eq_add_self` (2→1), `bool_true_or_false` (3→1, found a 3rd copy in `perfect.rs` beyond the brief's two) to `nat_prelude/ops.rs`; re-pointed 15 call sites across `irrational.rs`/`perfect.rs`/`primes.rs`/`powsq.rs`/`totient.rs`; census unchanged at 10/10 (tool is blind to private-fn duplication by construction) |
| 2026-08-28 | modeq-producer | conclusion-directed producer + axiom-free Lean contract close 10 open `nat.modeq` facts; `via_multi_target` 19 -> 30 |
| 2026-08-28 | modeq-producer | `Int.modEq_of_mul_right` closes the last open `integer-modular-equivalence` train fact, widening the Int shift family 5 -> 6 |
| 2026-08-28 | nat-log | `Nat.log` by structural fuel recursion — 2 definitions, 6 theorems, all axiom-free; 6 facts closed; `Nat.clog` sized as reachable by the same route |
| 2026-08-28 | `b67d472dc` | `Nat.factorial_dvd_factorial`/`factorial_le`/`factorial_lt_of_lt`/`factorial_ne_zero` admitted, axiom-free. |
| 2026-08-28 | `822c77a97` | fact: close `F:ml430-nat-factorial-ne-zero-5fc0b0a1`. |
| 2026-08-28 | `e0ca4c407` | fact: close `F:ml430-nat-factorial-dvd-factorial-e9d14845`. |
| 2026-08-28 | `aa391cd39` | fact: close `F:ml430-nat-factorial-le-d0f4a912`. |
| 2026-08-28 | `ddd2e0855` | fact: close `F:ml430-nat-factorial-lt-of-lt-d6c2125d`. |
| 2026-08-28 | nat-prime | `Nat.prime_odd_of_ne_two`, `Nat.prime_even_iff`, `Nat.prime_not_dvd_mul`, `Nat.prime_dvd_of_dvd_pow` admitted into the Nat prelude; closes 4 of 7 open `Nat.Prime` import facts |
| 2026-08-28 | nat-sqrt | `Nat.sqrt` by structural fuel recursion (accumulator fold, not the `logAux` shape) — 2 definitions, 2 theorems, all axiom-free; 2 facts closed (`F:nat-sqrt-zero`, `F:nat-sqrt-one`); 14 `F:ml430-nat-sqrt-*` mirror facts left open, sized for the next tier |
| 2026-08-28 | nat-clog | `Nat.clog` by structural fuel recursion, transferred verbatim from `Nat.log` — 2 definitions, 4 theorems, all axiom-free; 4 facts closed (`clog_zero_left`, `clog_zero_right`, `clog_one_left`, `clog_one_right`); `clog_pos`/`log_le_clog` sized as a separate generalized-induction task |
| 2026-08-28 | producer-widen | measured: conclusion-directed producer reaches 0 of 35 open non-held-out palette facts — 26 blocked at statement import, 9 induction-shaped |
| 2026-08-28 | producer-widen | new gated census: 61 of 63 open non-held-out propositions have an axiom-BEARING Mathlib proof, so transport cannot close the frontier; 6 guards each mutation-verified to kill exactly one control |
| 2026-08-28 | producer-widen | `scripts/provision-lean-import-toolchain.sh` — s4 CAN run the whole import route; pinned mathlib4 + lean4export provision in ~5 min |
| 2026-08-28 | nat-log-tier | `Nat.logAux_le_fuel` (fuel-generalized-over-`n` induction) and `Nat.log_le_self`, both axiom-free; 2 facts closed; `log_lt_self`/`log_mono_right` sized as genuinely harder, not attempted |
| 2026-08-28 | nat-bitwise | `Nat.bit` (non-recursive, no fuel needed) plus `bit_false`/`bit_true`/`bit_true_pos`/`bit_false_le_bit_true`, all axiom-free, all first-attempt kernel accepts; 4 new `F:nat-bit-*` facts; `Nat.bitwise`/`Nat.bits`/`Nat.ldiff` scoped out |
| 2026-08-28 | nat-gcd | 9 `natural-gcd` facts closed via the divisibility characterization of `Nat.gcd`/`Nat.lcm` (0 axioms) |
| 2026-08-28 | fib-backlog | `Nat.fib_add_two_strictmono`, `Nat.fib_strictmonoOn`, `Nat.fib_lt_fib` landed and kernel-checked (nat_prelude/fibonacci.rs); closed F:ml430-nat-fib-add-two-strictmono-c1e86d4d, F:ml430-nat-fib-strictmonoon-905810a9, F:ml430-nat-fib-lt-fib-3582b881 |
| 2026-08-28 | fib-backlog | confirmed `Int.fib` absent from the kernel (shape_search, fresh build, declarations=2000); all 6 open integer-fibonacci facts blocked on a missing carrier, not attempted |
| 2026-08-28 | int-bezout-witnesses | `Nat.xgcdAux`/`Nat.gcdA`/`Nat.gcdB`/`Int.gcdA`/`Int.gcdB` — extended Euclid as fuel-structural `Definition`s returning data |
| 2026-08-28 | int-bezout-witnesses | `Int.gcd_eq_gcd_ab_witnesses` — Mathlib v4.30's Bézout at named computable witnesses, axiom-free; closes `F:ml430-int-gcd-eq-gcd-ab-63005aef` |
| 2026-08-28 | nat-binomial | `Nat.choose_mono` via permuted `choose_le_choose`; closes `F:ml430-nat-choose-mono-a1af9c18`, kernel-lean, axiom-free; nat_prelude 447->448 |
| 2026-08-28 | nat-factorial-variants | `Nat.descFactorial` + `descFactorial_zero`/`_succ`/`_one`/`_of_lt`, axiom-free, `nat_prelude` sweep 105/105; 4 new `F:nat-desc-factorial-*` facts; `Nat.ascFactorial`/`Nat.multichoose` left for a future lane |
| 2026-08-28 | nat-primes-2 | `Nat.coprime_primes`, `Nat.not_prime_of_dvd_of_ne`, `Nat.Prime.pred_pos`, `Nat.succ_pred_prime`, `Nat.Prime.dvd_mul_of_dvd_ne` — five axiom-free kernel theorems in `nat_prelude/primes.rs`, five `natural-primes` facts flipped to `proved` |
| 2026-08-28 | int-build-time | measured: the flagged `int_prelude` regression is `cpoint_prelude_builds` caught by substring; Bézout costs +0.29 s, `CReal` prelude build went 12.2 s -> 108.4 s in two days |
| 2026-08-28 | nat-bitwise-2 | `Nat.land`/`Nat.landAux` (structural fuel recursion, direct — not through `Nat.bitwise`) plus `land_zero_left`/`land_zero_right`/`land_one_one`/`land_three_five`, all axiom-free, all first-attempt kernel accepts; 4 new `F:nat-land-*` facts; `Nat.bitwise`/`Nat.lor`/`Nat.ldiff`/`Nat.bits` scoped out |
| 2026-08-28 | int-gcd-2 | `Int.dvd_of_dvd_mul_right_of_gcd_one`/`Int.dvd_of_dvd_mul_left_of_gcd_one` -- `gauss_lemma` corollaries, axiom-free; closes `F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0`/`F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b` |
| 2026-08-28 | int-gcd-2 | `Int.gcd_greatest` -- the universal-property characterization of `gcd`, axiom-free; closes `F:ml430-int-gcd-greatest-5b31c5fe` |
| 2026-08-28 | supon-r6c | `CReal.meshLevelCount_pow` landed: cherry-picked alone from the broken `worktree-agent-a8d6d5209f5a4bb3d` branch, then fixed a SECOND bug (missing `lam_fv` wrap on the induction value) beyond the symm-argument fix the brief credited; `creal_prelude_builds` green |
| 2026-08-28 | creal-build-bisect | measured both endpoints (12.60 s at `77b71bf10`, 105.51 s at HEAD) and located the regression: `trig_fn` + `cos_sign` + `uniform_convergence`, all added 2026-08-27, are **79.0 s of 101.25 s**; the other 165 `STEPS` entries are 22.2 s combined |
| 2026-08-28 | creal-build-bisect | diagnosed the mechanism as unary-`Nat` reduction, **not** the `Definition` unfold: the hot declarations run 40–120 `unfold_def` attempts per successful δ-unfold (healthy is 1.6–3), 98% of them on `Nat.succ`/`Nat` towers, and cost is uncorrelated with term size (864 nodes / 9.74 s vs 8,174 nodes / 1.49 s) |
| 2026-08-28 | creal-build-bisect | A/B'd ADR-0614's literal numerals: **`CReal.cosWideNonpositive` 9.74 s → 0.12 s (81x)** and the whole build −11%, so the ADR's "measured at zero" (taken before these files landed) no longer describes this tree; the `trig_fn` family is unaffected and needs a proof change instead |
| 2026-08-28 | creal-build-bisect | `scripts/check-creal-prelude-build-ratio.sh` + `artifacts/creal-prelude-build-budget.tsv` + controls: replaces the ungated 94–123 s band with a **load-invariant ratio** against `rat_prelude_builds` (2.02x change in absolute time moves it 0.2%; the regression moves it 7.8x), pinned at 21, self-demonstrating on every run |
| 2026-08-28 | nat-lor | `Nat.lor`/`Nat.lorAux` (fuel recursion, `max`-via-`ble` per-bit step, `n`-returning fuel base case) + 3 boundary theorems in `nat_prelude/lor.rs`; wired into `nat_prelude.rs`; `nat_prelude_tests.rs` coverage + dedicated test + pinned render count `476->481`; 3 new `F:nat-lor-*` facts |
| 2026-08-28 | int-fib | `Int.fib : ℤ → ℤ` landed (`int_prelude/fibonacci.rs::declare_fib`), the sign-extended Fibonacci sequence, one `Int.rec` case split, axiom-free, evaluated at six concrete indices with a sign-drop negative control |
| 2026-08-28 | int-fib | `Int.fib_two_mul_add_one_pos` landed and kernel-checked, axiom-free; closed `F:ml430-int-fib-two-mul-add-one-pos-8977f65f` |
| 2026-08-28 | nat-modeq-gcd | land `Nat.ModEq.gcd_eq` (gcd.rs); confirm minFac absent, isRelPrime absent |
| 2026-08-28 | nat-modeq-gcd | land `Nat.div_dvd_div_left` (divisibility.rs) |
| 2026-08-28 | nat-modeq-gcd | land `Nat.coprime_of_dvd'` (primes.rs), fixing a build-order UnknownConst |
| 2026-08-28 | nat-asc-multichoose | `Nat.ascFactorial`/`Nat.multichoose` definitions + 6 boundary theorems + 6 new `F:nat-*` facts |
| 2026-08-28 | cas-reconstruct | `cas-certificate` `kernel-reconstructed` 1 → 3: registered two already-passing, unregistered CAS → kernel bridges; mutation-verified the degree-4 kernel check; measured the remaining 28 as a backlog, not a Richardson boundary |
| 2026-08-28 | evt-endpoint | `cas-certificate` `kernel-reconstructed` 3 -> 4: EVT endpoint exclusion for x^3-6x on [-3,2] admitted through `Kernel::add_declaration`, reusing the IVT sign-bracket bridge's engine verbatim; mutation-verified; registered as `F:cas-evt-endpoint-exclusion-cubic-kernel-checked`, a sibling of `F:cas-extremum-irrational-argmax` |
| 2026-08-28 | nat-factorial-dvd | falling/rising-factorial ↔ `choose` bridges + `factorial_dvd_descFactorial`/`factorial_dvd_ascFactorial`, closing 2 `F:ml430-nat-factorial-dvd-*` facts |
| 2026-08-28 | nat-ldiff | `Nat.ldiff`/`Nat.ldiffAux` (fuel recursion, `land`-shaped fuel-exhaustion base case, hybrid land/lor succ-row guard, `beq`+`bool_select_nat` per-bit step) + 4 boundary theorems incl. the asymmetry pair in `nat_prelude/ldiff.rs`; wired into `nat_prelude.rs`; `nat_prelude_tests.rs` coverage + dedicated evaluation test + pinned render count `492->498`; 4 new `F:nat-ldiff-*` facts |
| 2026-08-28 | nat-bitwise-general | landed `Nat.bitwise`, the general form `land`/`lor`/`ldiff` specialize; 5 new facts |
| 2026-08-28 | fib-2 | `Nat.le_fib_self` (kernel-checked, axiom-free), closing `F:ml430-nat-le-fib-self-0cbccb4d`; `Nat.le_fib_add_one`/`Int.fib_add`/`Int.fib_of_odd` re-diagnosed and left open with sharper blockers |
| 2026-08-28 | int-parity | `Int.Even`/`Int.Odd` via `natAbs`, two bridge theorems, `Int.fib_of_odd`, all axiom-free; `F:ml430-int-fib-of-odd-66560495` proved |
| 2026-08-28 | nat-bounded-cases | `ops::cases_lt_bound`/`cases_lt_or_ge`/`cases_lt_bound_absurd` (general bounded-case infrastructure); `Nat.le_fib_add_one` and `Nat.Prime.five_le_of_ne_two_of_ne_three` (kernel-checked, axiom-free), closing `F:ml430-nat-le-fib-add-one-5284f0bf` and `F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786` |
| 2026-08-28 | nat-descfact-lemmas | `Nat.descFactorial_self` (`n.descFactorial n = n!`, via the existing `descFactorial_eq_factorial_mul_choose` bridge at `k := n` plus `choose_self`/`mul_one`); closes `F:ml430-nat-descfactorial-self-899fc0e0` |
| 2026-08-28 | nat-descfact-lemmas | `Nat.descFactorial_le` (monotone in the base for fixed exponent: `k <= m -> k.descFactorial n <= m.descFactorial n`, via `choose_le_choose` + `mul_le_mul_left` + two transports across the bridge equation); closes `F:ml430-nat-descfactorial-le-2b8cc09a` |
| 2026-08-28 | nat-descfact-lemmas | `Nat.self_le_factorial` (`n <= n!`, direct induction on `n` using `one_le_factorial`, independent of the `descFactorial`/`choose` bridge); closes `F:ml430-nat-self-le-factorial-cfdffc69` |
| 2026-08-28 | nat-descfact-lemmas | `F:ml430-nat-descfactorial-of-lt-fbcf5d26` status flip only — `Nat.descFactorial_of_lt` already existed and already matched the fact's `formal.statement` verbatim; attached evidence (kernel-term + axiom-footprint checkers) and flipped `epistemic_status` to `proved`, no new proof work |
| 2026-08-28 | nat-multichoose-facts | Confirmed (via Mathlib source at the pinned commit) that our `Nat.multichoose` is a formula-based definition while Mathlib's is a genuine double recursion, so the three `ml430` multichoose mirror facts correctly stay `open`; no code or fact changes needed, all three theorems and their local facts were already proved by the prior lane. |
| 2026-08-27 | (uncommitted at status-file write time) | `CReal.sumRange_cauchy_of_abs_cauchy` / `CReal.sumRange_converges_of_abs_converges` (absolute convergence implies convergence) plus a soundness-negative control; curriculum rows 18 and 22–23 corrected. |
| 2026-08-27 | (uncommitted at status-file write time) | Ten new `artifacts/facts/F-creal-*.json` entries for the Ch.13/14 Riemann integral construction and algebra (`riemannSum_cauchy`, `integral`, `integral_converges`, `integral_const`, `integral_add`, `integral_le`, `integral_scale`, `integral_witness_independent`, `riemannSum_integral_close`, `sharedIndexToCanonical`); `python3 scripts/validate-facts.py` green (708 facts, 0 errors). |
| 2026-08-27 | (uncommitted at status-file write time) | Added `--require-declaration <name> [--require-kind <kind>]` to `crates/axeyum-lean-kernel/examples/kernel_declaration_projection.rs`: a direct, fail-on-absence presence checker for `Declaration::Definition`s (and any other kind), mutation-tested against `CReal.integral`. Upgraded `F:creal-integral`'s `kernel-CReal.integral` evidence to use it. Registered 14 new `artifacts/facts/F-creal-*.json` entries for Spivak Ch.18 (`e`) and Ch.22-23 (series convergence tests): `creal-e`, `creal-e-converges`, `creal-two-le-e`, `creal-e-le-three`, `creal-e-le-four`, `creal-expterm-le-geom`, `creal-expdominantcauchy`, `creal-cauchyofpointwiseequiv`, `creal-geomcauchy`, `creal-sumrange-comparisontest`, `creal-sumrange-cauchy-of-dominated`, `creal-sumrange-converges-of-dominated`, `creal-sumrange-cauchy-of-abs-cauchy`, `creal-sumrange-converges-of-abs-converges`. `python3 scripts/validate-facts.py` green (722 facts, 0 errors). |
| 2026-08-27 | (uncommitted at status-file write time) | Registered 28 new `artifacts/facts/F-*.json` entries: Ch.15 cosine-at-1 construction and bounds (`creal-cosone`, `creal-costerm`, `creal-cosseriespartial`, `creal-costermabsledominant`, `creal-cosoneconverges`, `creal-cosone-le-four`, `creal-neg-four-le-cosone`); Ch.22-23 general-ratio geometric series and ratio test (`creal-geomcauchyoflt`, `creal-geomcauchyofltordered`, `creal-geomscaledcauchyoflt`, `creal-sumrangeratiotest`); Ch.14 crossing-index construction (`creal-crossingindex`, `creal-crossingupper`, `creal-crossinglower`, `creal-crossingsampleupper`, `creal-crossingsamplelower`); Ch.25-27 polynomials over `Complex` (`complex-polyeval`, `complex-polyeval-zero`, `complex-polyeval-succ`, `complex-polyadd`, `complex-polyeval-polyadd`, `complex-polyscale`, `complex-polyeval-polyscale`, `complex-polydegreelt`, `complex-polydegreelt-polyadd`, `complex-polydegreelt-polyscale`, `complex-polymul`, `complex-polyeval-polymul`). `python3 scripts/validate-facts.py` green (750 facts, 0 errors). Mutation-tested 3 representative checkers (1 definition, 2 theorems) in an isolated snapshot; all failed correctly on the mutated name while unrelated controls in the same rebuild passed. |
| 2026-08-27 | `PENDING` | Diagnosed why `fact-frontier.py --json` reports `admissible: 0` over 132 dependency-ready facts: operation registration requires a completed, independently-checked proof (`ADMISSION_CONTRACTS` allows only `proved`), and none exists for any open fact. Added a purely additive `diagnostics.unregistered_by_route_class` split to `fact-frontier.py`; declined to fabricate an operation over unproved work. `docs/autogenesis/288-admission-precedes-registration.md`. |
| 2026-08-27 | `PENDING` | Implemented ADR-0602: `artifacts/ontology/producer-contract.schema.json` + `scripts/validate-producer-contracts.py` (a capability claim, never a completion claim — no `proved`/`epistemic_status` field exists in the schema at all), two seed contracts (Int.ModEq congruence family, Nat.Coprime family — both checked held-out-clean against `nursery-v1.json`), and redefined `fact-frontier.py` admissibility as dependency-ready × (registered operation OR matched capable-route contract). `admissible_count` moved 0 → 27 on the real ledger; all 8 existing `test_fact_frontier.py` tests pass unmodified, 7 new added. `docs/autogenesis/289-producer-contract-admissibility.md`. |
| 2026-08-27 | `PENDING` | Sharded `creal_tests.rs`'s single 432-entry pinned inventory array into 33 per-module `Vec`s under new `crates/axeyum-lean-kernel/src/creal/inventory/`, registered from a new `creal/inventory.rs`; `creal_tests.rs` now derives coverage from the union plus a new duplicate-across-shards check, both mutation-verified; no per-shard pin (superseded by the environment-derived assertion). Purely additive one-line change to `creal.rs` (`mod inventory;`); no existing `creal/*.rs` module content touched. Updated `scripts/recount-pinned-inventory.py`/its test controls and `CLAUDE.md`'s pin-guidance sections for the new shape. |
| 2026-08-27 | `cb8b54e20` (+fixups) | Setoid congruence deriver: new `creal/congruence.rs` (registry of 6 congruence lemmas + `Op`/`Arity`/`CongruExpr`/`derive`/`declare_derived_congr`) and `creal/inventory/congruence.rs`; one permanent registration `CReal.mulPowCongr` (power-series term congruence) dispatched from `build_creal_prelude_uncached`; four kernel-checked demos plus a negative control and its mutation test. One new `CRealPrelude` field (`mul_pow_congr`). No other `creal/*.rs` module touched. |
| 2026-08-27 | `PENDING` | First real execution of a producer-contract dispatch (`F:ml430-int-add-modeq-left-ee732b5b`): clean s5 export/import, honest producer decline (`TerminalNotClosed`), recorded as a decline artifact + fact note rather than a fabricated admission. No fact status changed, no operation registered. |
| 2026-08-27 | `e0c96569e` | Contract-decline convention (doc 291): `contract_sha256` re-dispatch key added to the seed decline artifact; new `scripts/validate-producer-contract-declines.py` (25 tests). |
| 2026-08-27 | `96e40ce3d` | `scripts/fact-frontier.py` reads decline artifacts as selector input: live-decline computation, three-population diagnostics, `declined_fact_ids`. Selection moves off the declined fact. |
| 2026-08-27 | `cdc10b413` | Wired the decline validator into `scripts/check.sh`, `justfile`, and an 8-guard mutation suite in `scripts/tests/mutation_controls.py` (all killed). |
| 2026-08-27 | `8eb74e605` | `rat_prelude/cas_ivt_bridge_tests.rs`: CAS IVT sign-bracket sign bracket kernel-reconstruction, 2 passing tests, paired accept/reject. |
| 2026-08-27 | `7705b0776` | feat(cas): exact polynomial EXTREMUM certificate (ADR-0603 row 3, EVT) |
| 2026-08-27 | `86d888a82` | wip(cas): scaffold `extremum` module for ADR-0603 row 3 (EVT) |
| 2026-08-27 | `PENDING` | Batch dispatch over all 26 currently admissible facts (11 `int-modeq-family-v1`, 15 `nat-coprime-family-v1`). Result: 26 honest declines, 0 proofs — 11 clean-import `TerminalNotClosed` (int-modeq, matching turn one's mechanism), 15 import-stage `TrustedDeclaration` (nat-coprime, a new finding this batch's own predictions missed). After state: admissible_count 0, declined_count 27, selection refused-no-admissible-candidate. All validators green. |
| 2026-08-27 | `f9dee8754` | `CReal.uniformlyContinuousOn_restrict` — the sub-interval `UniformlyContinuousOn` restriction `integral_split`'s assembly needs; same modulus, `le_trans`-composed range hypotheses, kernel-checked. |
| 2026-08-27 | `31aea5551` | docs(integral): pin down exactly what estimate work remains to close `integral_split` — the `l`-shrinks-via-`depth` lever and the `total_eps_sample_le` generalization, so the next lane does not re-derive this. |
| 2026-08-27 | `6bdb1e35f` | ADR-0605 3: `LraReconstructCtx::new`/`::try_new` renamed to `new_over_axreal`/`try_new_over_axreal`, `Default` removed, every call site updated, `axreal_call_site_guard` added (3 tests, proved discriminating by hand). `cargo test -p axeyum-solver --lib --features full` 1435/0 failed; `farkas_over_the_integers` 9/9; `front_door_reaches_no_real_axiom`/`sos_lean_reconstruct` 1/1, 14/14 (release). |
| 2026-08-27 | `c86fadafe` | Five `Int.ModEq` shift-family facts joined to `authoritative-kernel-int-modeq-shift-family-v1` via a minimal `checker_operation.id` evidence row (no fabricated receipt fields — no executor case exists for this driver). `validate-facts.py` 806/0; ledger `facts_via_multi_target` 14 -> 19. |
| 2026-08-27 | `4724bc38a` | feat(cas): polynomial_mvt -- exact Mean Value Theorem on the decidable fragment |
| 2026-08-27 | `85b0af141` | fix(cas): mvt fixes -- clippy option_option, two failing tests, measured cost curve |
| 2026-08-27 | fact-gen | `scripts/gen-kernel-facts.py` + 32-test suite + `mutation_controls.py kernel-facts` (13 guards); 64 generated `string` facts (0/64 → 64/64); ledger coverage 34% → 38.5%; ADR-0607; one `KERNEL_THEOREM_RE` alternative in `validate-facts.py` |
| 2026-08-27 | (uncommitted at status-file write time) | Registered 12 facts: `F:creal-riemannsum-split-exact`, `F:creal-riemannsum-split-scale-invariant`, `F:creal-riemannsum-split-exact-of-uc`, `F:creal-congrofuniformlycontinuous`, `F:creal-uniformlycontinuouson-restrict`, `F:creal-close-within-of-within-indexed`, `F:creal-riemannsum-sharedaccuracyclose-at`, `F:creal-powerseriesterm`, `F:creal-powerseriesterm-congr`, `F:creal-powerseriesterm-abs-le`, `F:creal-powerseriesuniformconvergeson`, `F:creal-mulpowcongr`. |
| 2026-08-27 | (uncommitted at status-file write time) | Added `scripts/gen-ledger-coverage.py` + `scripts/tests/test_gen_ledger_coverage.py` (26 tests) + `scripts/tests/mutation_controls.py` `ledger-coverage` suite (7 guards) + `artifacts/ledger-coverage.json` + one-line registrations in `scripts/check.sh` and `justfile`. Headline: 1,397 kernel theorems, 474 registered, 923 unregistered (34%). |
| 2026-08-27 | `DONE` | `graded-statement-families.md` MVT row 3 refreshed to landed; FTA row 3/row-2-applicability independently re-assessed with fresh positive/negative controls, a sized cheapest-route estimate (RUR), and a finding that FTA may be a three-row theorem with no row 2; `spivak.md` row 11 corrected to match. |
| 2026-08-27 | ledger-ratchet | `registered`/`curated` split in `scripts/gen-ledger-coverage.py`; convention `absent-field-is-curated` printed in the output; 4 mutation controls in `mutation_controls.py`; 7 tests in `test_gen_ledger_coverage.py` |
| 2026-08-27 | fact-gen-nat | Ran `scripts/gen-kernel-facts.py` (unmodified) over `nat` (250 planned, 2 declined) and `creal` (247 planned, 0 declined); registered 497 generated facts; coverage 538/1,409 (38.5%) → 1,026/1,409 (72.8%), `curated` unmoved at 474; found and traced a 9-theorem `Nat.Peano.*` gap between `kernel_declaration_projection` and `prelude_theorem_inventory` |
| 2026-08-27 | denominator | Added the missing `characterization` group (`Nat.Peano.*`, `Int.Characterization.*`, 32 axiom-free theorems) to `prelude_theorem_inventory`'s `build_groups`, confirming `kernel_declaration_projection` was already correct; updated `gen-theorem-production-ledger.py`'s `EXPECTED_PRELUDES` and regenerated its ledger doc; regenerated `artifacts/ledger-coverage.json` (kernel_theorems 1,416→1,448, registered 1,026→1,035, curated unmoved at 474); added `scripts/check-theorem-inventory-completeness.py` + 9 unit tests, mutation-verified, so the two tools' theorem-name-set agreement is a standing, checkable guard rather than a fact-generation lane's accidental find |
| 2026-08-27 | collision-gap | Wired `build_characterization` into `cross_prelude_collision_tests.rs`'s `build_groups` at the same dependency-order position the other two theorem/declaration inventory tools use; confirmed no cross-prelude name collision exists for the 32 `Nat.Peano.*`/`Int.Characterization.*` declarations. Extended `scripts/check-theorem-inventory-completeness.py` with a three-way prelude-group-label agreement check (`kdp_prelude_labels`/`pti_prelude_labels`/`collision_group_labels`/`check_group_labels`) so a fourth prelude group omitted from any of the three `build_groups` implementations fails loudly instead of silently; 9 new unit tests (20 total), all 6 new guards mutation-verified with no survivors after fixing a stale-`__pycache__` false-kill in the mutation sweep itself. |
| 2026-08-27 | (pending commit) | Fix `Nat.succ_sub_succ_eq_sub` (`nat_prelude/order_extra.rs`) to reuse `succ_sub_succ`'s proof term instead of an independent re-derivation, matching the file's own alias pattern; adjudicate all 10 `shape_search --duplicates` groups in `docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`. |
| 2026-08-27 | (pending commit) | Fix the `rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound` accidental duplicate: `sample_upper_bound`/`sample_lower_bound` (`creal/uniform_continuity.rs`) now forward to `rat_approx_upper`/`rat_approx_lower`'s proof term instead of re-deriving; direction chosen by build order, not consumer count. Add `scripts/check-shape-duplicates.py` + `scripts/shape-duplicates-allowlist.json`, a mutation-verified gate (8/8 guards killed) so a new `shape_search --duplicates` group must be read and either fixed or allowlisted with a reason. |
| 2026-08-27 | fact-refresh | 423 generated facts merged (6 quarantined on `KERNEL_THEOREM_RE`, since regenerated); `registered` 1,038 -> 1,461; `curated` unmoved at 474 |
| 2026-08-27 | 150-allowlist | see this lane's detail above |
| 2026-08-27 | (pending commit) | ADR-0611 + `scripts/check-absence-claims.py`: an absence claim in prose carries `<!-- absent: Root.name -->` and the gate fails the moment that declaration exists in `kernel.environment()` — `#[expect(dead_code)]` for documentation. `<!-- was-absent: … -->` is checked in the opposite direction so a historical record cannot point at nothing. Seeded on four of the five known-stale records of 2026-08-27 (the fifth, `trig_fn.rs`, verified still literally true); demonstrated red-then-green by `scripts/tests/demo-absence-expiry-seeds.sh`; 25/25 guards mutation-killed, 0 survived, 0 unmeasured. Adoption printed on every run: 4 of 145 checkable claim sites annotated (one of them a LIVE `absent:` claim on `CReal.within_of_close_within`, which reds the day that bridge lands), 141 not, 560 sites structurally uncheckable. |
| 2026-08-27 | 152-restate-sweep | see this lane's detail above |
| 2026-08-27 | `f6ebbd24a` | Share `equiv_of_sub_equiv_zero`: `deriv_unique.rs` (canonical) ← `exp_fn.rs`. |
| 2026-08-27 | `2f3bb6195` | Share `abs_neg_le`: `uniform_continuity.rs` (canonical) ← `exp_fn.rs`; delete orphaned `double_neg` in `exp_fn.rs`. |
| 2026-08-27 | `0880356d8` | Share `abs_neg_equiv`/`abs_of_nonneg`/`le_sub_of_add_le`: `deriv_unique.rs` (canonical) ← `fermat.rs`; delete orphaned `le_abs_neg_of_le_abs` in `fermat.rs`. |
| 2026-08-27 | `780eb52f1` | Share `add_sub_cancel`: `deriv_unique.rs` (canonical) ← `fermat.rs`; document the two genuinely-different same-named helpers in `convergence.rs`/`uniform_continuity.rs`. |
| 2026-08-27 | `e8a444879` | Share `neg_zero_equiv` (7 copies -> 1): `series.rs` (canonical) ← `derivative.rs`, `fermat.rs`, `geometric.rs`, `mvt.rs`, `power.rs`, `rolle.rs`. |
| 2026-08-27 | `be5fed9ad` | Derive python control registration; delete `PY_ORPHAN_BASELINE=188`. 7 guards, 12/12 mutation-killed; `py_orphans` 188 → 0. |
| 2026-08-27 | `b47deeb93` | `run-python-controls.py` + `control-optout.tsv`: 169 suites / 1193 tests now run; 9 pytest-dialect suites unwrapped from collecting zero tests. |
| 2026-08-27 | `a94a19480` | Open the lane; record the starting measurement. |
| 2026-08-27 | (pending commit) | Triage the 12 red drift detectors from `docs/plan/status/154-inert-controls.md`: 1 test-mock bug fixed (`test_check_autogenesis_nat_fib_gcd_surface_plan`, mutation-verified), 11 root-caused and left excluded with precise reasons in `control-optout.tsv` (stale pins after legitimate refactors/doc changes, one over-broad Cargo.lock pin, one `git safe.directory` false negative, one genuine "target fact got proved" happy drift, one genuine shared-artifact drift). `OPTOUT_CEILING` 19 -> 18. Also repaired `scripts/check-shell-antipatterns.sh` (red on `main`): fixed the in-scope `grep -q` in `scripts/tests/test-lane-commit.sh`, baselined the out-of-scope one in `render/check.sh`. |
| 2026-08-27 | ftc | `integral_abs_le_of_bound`, `integral_sub_linear_le`, `antiderivative`, `antiderivative_abs_le` — all first-attempt, axiom-free; rung 3 characterised as three lemmas, none an estimate |
| 2026-08-27 | ftc-rung3 | `CReal.hasDerivative_antiderivative` — **FTC-I**, axiom-free, first attempt — with `clamp_mono`, `clamp_id`, `max_sub_min`, `min_mono_left`, `max_mono_right` and `integralSplitAnywhere` (`integral_split_arbitrary` with its `PosBound` removed; `inv_index_irrelevant` was NOT needed) |
| 2026-08-27 | cos-deriv | `CReal.abs_diff_le_of_deriv_bound` -- mean value inequality; `monotone_of_nonneg_deriv` applied twice, to `r ↦ M·r ∓ F(r)`; axiom-free |
| 2026-08-27 | `creal/mvt.rs::build_hd_linear` → `pub(super)` | reused rather than copied; `hasDerivative_smul ∘ hasDerivative_id` would need a magnitude bound on `M` |
| 2026-08-27 | measured: uniform-limit-of-derivatives is ABSENT | `shape_search` at `declarations=1889`; 16 `HasDerivativeOn` conclusions, all pointwise |
| 2026-08-27 | (pending commit) | Absence-claim marker coverage: 4/145 -> 18/147 checkable sites (70 `docs/`-owned BARE candidates examined by hand, 15 marked, 55 rejected as not genuine kernel-absence claims). 7 stale "does not exist" claims found and corrected to `was-absent:` with a historical-record note (`Nat.le_refl`, `CReal.sqrt`, `CReal.alternatingBracketUpper`/`alternatingLowerBound`/`alternatingUpperBound`, `CReal.uniform_converges_add`, `Nat.even_or_odd`, `Rat.abs` x3 independently across three documents, `Rat.le`, `Rat.sub`). 8 new live `absent:` markers on currently-true claims (`Complex.exp`/`arg`/`fundamentalTheoremOfAlgebra` x3 sites, `Complex.le`/`lt`, `CReal.within_of_close_within`, `CReal.sup`, `Nat.div_add_mod`). Gate green throughout; `crates/` findings reported, not edited. |
| 2026-08-27 | `7d08d970f` | `CReal.ivt_exact_root_at` — Ch12 inverse existence via shifted IVT, wrapping `ivt_exact_root` around `F − y`. |
| 2026-08-27 | `adbfdee31` | rustfmt the above commit's touched files. |
| 2026-08-27 | uniform-deriv | `CReal.hasDerivative_uniform_limit` -- the uniform limit of derivatives; first `HasDerivativeOn` conclusion in the tree from a limit hypothesis; axiom-free, first-attempt kernel accept |
| 2026-08-27 | uniform-deriv | `CReal.lipschitz_of_deriv_bound` -- the mean value inequality for an UNORDERED pair, via `min x y` and no case split; the keystone lane 159's plan did not anticipate |
| 2026-08-27 | uniform-deriv | `CReal.abs_diff_sub_le_of_deriv_bound` -- the tail estimate `\|(F y - F x) - (G y - G x)\| <= sup\|F' - G'\|*\|y - x\|` |
| 2026-08-27 | uniform-deriv | measured: `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn` ABSENT at `declarations=1890`, FOUND 1 at 1893 |
| 2026-08-27 | uniform-deriv | 14 `creal/derivative.rs` helpers promoted to `pub(super)` and imported rather than copied |
| 2026-08-27 | ratint | `verify_horowitz`: independent poly-arithmetic checker for the Horowitz rational-part split, 6 guards, all mutation-verified |
| 2026-08-27 | ratint | `verify_log_terms`: independent poly-arithmetic checker for the Rothstein–Trager log-part decomposition, 3 guards, all mutation-verified |
| 2026-08-27 | ratint | 22 unit tests added to `ratint.rs` (was 0): producer sanity, positive roundtrips with an eval cross-check, and adversarial fixtures per guard, including two flagship "vacuous without this guard" fixtures |
| 2026-08-27 | ratint | Removed 2 guards proven always-subsumed (verify_log_terms's duplicate-v check; verify_horowitz's original D2/D1-nonzero check, replaced by an explicit denom-non-constant guard) rather than leave them as decoration |
| 2026-08-27 | ftc2 | `CReal.integral_eq_antideriv_diff` — **FTC-II** (the evaluation rule, `∫ₐᵇ F = G(b) − G(a)` for ANY antiderivative `G`), axiom-free, first attempt — via `constant_of_zero_deriv` on `G − antiderivative F a b hab u`, two applications of a new shared `integral_zero_of_width_zero` (degenerate-interval integral is `Equiv`-zero, closed through `mul_self_abs`/`eq_zero_of_mul_self_zero` rather than the rational `equiv_zero_of_small` route), and one general rearrangement lemma `eq_sub_comm` |
| 2026-08-27 | cas-audit | mutation-verified tests for `MvPoly::derivative_in`, `Monomial::exponent_of` (mvpoly.rs) and `geometry_certify::same_point`, found untested despite being reachable from Python bindings; census of 709 pub items found the crate's apparent test gaps mostly resolve via non-`cargo-test` coverage (CLI subprocess tests, `scripts/check-sos-negative-controls.sh`), with `geometry_json::condition_of` and `boolean_anf::variable_count` confirmed genuinely dead |
| 2026-08-27 | cos-deriv2 | `CReal.cosFnPartialHasDerivative` -- lane 159 step 1: every `n+1`-term partial sum of cosine's series differentiates to minus the `n`-term partial sum of sine's; kernel-accepted, `creal_prelude_builds` 93.18 s green |
| 2026-08-27 | cos-deriv2 | `CReal.expTermSuccScale` + `CReal.cosFnTermDerivCoeff` -- the index-shifted coefficient identity priced at ~70 lines: an `Eq` between two `Rat.normalize`s is ONE `normalize_congr`, where the `<=` between the same two terms (`exp_term_antitone_rat`) is ~130 lines of `Int` cross-multiplication |
| 2026-08-27 | cos-deriv2 | measured: `hasDerivative_pow`'s two Skolem `BoundedOn` functions cost one `d.lam_fv` each -- `trig_fn.rs` already had `pow` uniform continuity at a symbolic exponent, inline and duplicated; `bounded_of_uniformly_continuous` computes the index |
| 2026-08-27 | cos-deriv2 | measured: the `succ n`/`n` index shift does NOT reach `hasDerivative_congr` (`sumRange`'s ι-reduction makes both function sides defeq); it bites at `hasDerivative_uniform_limit`, and the missing fact is one-step antitonicity of `Rat.natDivSucc` in its INDEX at a symbolic numerator -- `natDivSucc_antitone` is numerator-1, `natDivSucc_le_scaled` wants a `(c+1)n+c` index |
| 2026-08-27 | cos-deriv2 | `trig_fn.rs`'s inline `pow_uc` induction extracted to `pow_uc_fn` from two byte-identical copies; 4 more `derivative.rs` helpers promoted to `pub(super)` rather than reproduced |
| 2026-08-27 | cos-deriv2 | `CReal.cosFnWideHasDerivative` -- **the target**: `HasDerivativeOn cosFnWide (fun x => neg (sinFn x)) zero (8/5)`, axiom-free, accepted on the first `add_declaration`; `creal_prelude_builds` 98.76 s green, `every_creal_declaration_is_checked_and_axiom_free` (`--release`) 15.22 s green |
| 2026-08-27 | cos-deriv2 | `CReal.natDivSuccStepLe` -- one-step antitonicity of `Rat.natDivSucc` in its INDEX at a symbolic numerator, the fact `rat_prelude` lacks and every `UniformConvergesOn` re-indexing needs; via `natDivSucc_mul` factoring the index into the numerator-1 factor, no new cross-multiplication. Belongs in `rat_prelude`; parked in `CReal` because that file is another lane's |
| 2026-08-27 | cos-deriv2 | `CReal.uniformConvergesShift` + `CReal.uniformConvergesNeg` -- re-index a uniform-convergence witness by one, and negate one; both leave the rate unchanged |
| 2026-08-27 | intparts | `CReal.integral_by_parts` — integration by parts, axiom-free, second attempt (one `arrow`-vs-`pi_fv` bug, diagnosed and fixed) — via `has_derivative_mul`, FTC-II (`integral_eq_antideriv_diff`), `integral_add`, and the shared private `add_cancel_right` |
| 2026-08-27 | intparts | Substitution (chain-rule composition) characterised as BLOCKED by `hasDerivative_chain`'s own hypotheses, not merely sized as harder: the outer function's `HasDerivativeOn` shares the inner function's exact `[a,b]`, and the inner function must self-map `[a,b] → [a,b]`, so a range-changing substitution cannot be invoked at all — a new chain-rule variant with an independent outer domain is needed, not a composition of landed pieces |
| 2026-08-27 | supon5 | `CReal.expOfModulus`/`trueExpOfModulus` (supOn rung 5, accuracy-selection schedule) — 5 declarations, all kernel-verified, all axiom-free |
| 2026-08-27 | pi | `CReal.cosFnWide_one_equiv_cosOne` + `CReal.cosFnWide_one_nonneg` -- rung 1 of pi: `cos 1 >= 0` for the wide FUNCTION. `cosOne_nonneg` was not this fact, and `cosFn_one_equiv_cosOne` is about the NARROW `cosFn` on `[0,1]`; both accepted first try, `creal_prelude_builds` 99.32 s green |
| 2026-08-27 | pi | measured: `declare_cos_fn_equiv_cos_one`'s body never mentions the interval -- factored to `cos_limit_at_one_equiv_cos_one(u_conv, hab_lo, hab_hi)` and reused verbatim for the wide domain; the narrow statement is unchanged |
| 2026-08-27 | pi | `CReal.hasDerivativeOn_restrict` -- the sub-interval restriction of a DERIVATIVE witness, the counterpart `uniformlyContinuousOn_restrict` has had since `integral_split`; same modulus, `spec` reused via `le_trans`. Accepted first try, `creal_prelude_builds` 106.57 s green. Belongs in `creal/derivative.rs`, parked in `trig_fn.rs` because that file is another lane's |
| 2026-08-27 | supon6 | `creal/supremum.rs` module doc: corrected rung 6's plan — the "constant-multiple corollary" already exists (`mul_ordered_half_body`/`promote_ordered_half_to_full`/`cauchy_of_abs_diff_le`); the real blocker is an unattempted multi-level nearest-mesh-point gap bound, documented with two candidate routes. No new kernel declarations. |
| 2026-08-27 | pi-rung2 | `CReal.converges_upper_bound_shift` -- `forall s f L b, (forall n, le (f (add n s)) b) -> Converges f L -> le L b`. `alternating.rs` says in its own doc comment that this does not exist and then runs the negation route INLINE on one concrete sequence: hiding place 2, one declaration from reusable. Accepted first try, `creal_prelude_builds` 95.38 s green |
| 2026-08-27 | pi-rung2 | `CReal.alternatingUpperBoundTail` -- the Leibniz upper bound needing antitonicity only from index 1, which is what cosine at `8/5` has (`a 0 = 1 < a 1 = 32/25`, tail antitone). General in `a`, not tied to cosine |
| 2026-08-27 | pi-rung2 | measured NEGATIVE: the shifted-series route `169-pi.md` proposed is blocked by `Converges`'s own definition, not merely unbuilt -- it is a UNIFORM-rate condition constraining index `0`, so any eventually-equal transfer has an index-`0` obligation that an arbitrary `g 0` cannot discharge. The re-indexed series' partial sums agree with the shifted originals only from `n = 1` |
| 2026-08-27 | `14a6484d3` | `scripts/validate-facts.py`: classify `cas-certificate` evidence as `kernel-reconstructed` vs `cas-internal`, reject an unclassifiable checker_command on that route (ADR-0601 SS2). Mutation-tested. |
| 2026-08-27 | `17e91d839` | `scripts/gen-import-backlog.py` (new): produce `artifacts/import-backlog.json`, the 164-row import backlog, deterministic and ordered by dependency-readiness then curriculum-DAG position (ADR-0601 SS3). `--check` wired into `scripts/check.sh` and the `justfile`. Mutation-tested. |
| 2026-08-27 | `de853af65` | Level-1 fix: `STEPS` (135 entries) + `validate_step_order` structural preflight for `creal.rs`, replacing the hand-written `declare_*` sequence in `build_creal_prelude_uncached` with `for step in STEPS { (step.run)(&mut d, prelude)?; }`. 0 violations across 2,264 edges against the existing order. `cargo check -p axeyum-lean-kernel --lib` clean, 0 warnings. |
| 2026-08-27 | `146927d8f` | Deliberate-failure controls + order pin: `steps_table_matches_recorded_extraction`, `existing_step_order_is_topologically_valid`, `order_violation_is_detected_and_precise`, `order_violation_reports_missing_provider_as_table_bug`. All green; failure controls verified to actually fail via a temporary mutation, reverted. `every_creal_declaration_is_checked_and_axiom_free` green (debug and `--release`). |
| 2026-08-27 | `1006ea4f1` | `nice` does not cross a session boundary; `CPUWeight` on a sibling slice does. Three instances of one failure shape in this wrapper now — `MemoryMax` without `MemorySwapMax`, `nice` under autogrouping, and `CPUWeight` at the wrong cgroup level twice. Each was genuinely applied, each read back correctly, each worth nothing. The rule: a control for a resource policy must assert the **relation** (sibling level, swap ceiling, scheduling domain), never only the value — the value check is the comfortable check that cannot fail. |
| 2026-08-27 | `3684f24aa` | Controls, mutation-verified. The case that carries the suite is a real deadlock probe: every slot held, the re-entrant job must complete **and** the non-re-entrant one must report 75 — without the second half the first passes on any host where slots were never contended. The harness mutates a four-file scratch copy, never the checkout: these are shell scripts read fresh on every invocation, so an in-place mutant is executed by any lane running a gate during the window. |
| 2026-08-27 | `82f411fa6` | The semaphore wired into `check.sh` (one slot per run, re-entrant, no memory scope on the supervisor), the battery at nice 0 with an advisory fail-open slot, and `Cargo.lock` added to the change filter. `check.sh`'s step list verified byte-identical, so `check-aggregate-scope.sh` is unaffected. |
| 2026-08-27 | `afa659d62` | First diagnosis commit — and its "positive control" was wrong in the way this repository keeps documenting: `grep -c cargo-serialized scripts/local-ci.sh -> 1` matched a **comment**, not a call, so a control certified a query that was measuring nothing. Corrected in the same document rather than quietly fixed. |
| 2026-08-27 | `DONE` | ADR-0603's four remaining graded statement families (MVT, LUB, Taylor remainder, FTA) stated as measured rows in `docs/curriculum/graded-statement-families.md`; two stale `spivak.md` claims corrected (`Complex.abs`/`CReal.sqrt` no longer absent; `Complex.polyMul` no longer blocked); ADR-0603 given a pointer postscript. |
| 2026-08-27 | (pending) | `Int.modEq_add_mul_left` + five corollaries (`Int.add_modEq_left`, `Int.add_modEq_right`, `Int.mod_modEq`, `Int.modulus_modEq_zero`, `Int.modEq_sub`) in `crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`, proved unconditionally in the modulus via `case_split` on `Int.rec` shape — no `0 < n` hypothesis anywhere, closing five of doc 292's eleven declined `Int.ModEq` facts. `derived_laws` recounted 126 → 132 (counted, not incremented). New concrete-instantiation test at n := 0/5/-4, mutation-verified. Five facts flipped `open` → `proved`; five decline artifacts amended (not deleted). `cargo test -p axeyum-lean-kernel --lib`: 832 passed, 0 failed. |
| 2026-08-27 | (pending) | New `axeyum-lean-kernel/authored-declaration-v1` execution driver in `scripts/validate-autogenesis-operations.py` (re-checkable fields: declaration source/test file existence, literal declaration-in-source check, literal test-function-in-file check, fact-id binding order); registered doc 293's five `Int.ModEq` closures as one operation; ten discrimination tests + eight mutation-verified guards; ADR-0602 amendment; `docs/autogenesis/296`; regenerated `docs/plan/generated/production-provenance-ledger.md`. |
| 2026-08-27 | `00797f01d` | Level-1 fix: `STEPS` build-order table + `validate_step_order` structural preflight, replacing the 89-call hand-written sequence in `build_complex_prelude`. `cargo check` clean. |
| 2026-08-27 | `e0984768a` | Part B: real (not simulated) module split for `poly.rs` (21 fields into `poly::PolyNames`, 144 call sites rewritten). Full suite: 48 passed / 0 failed in 441.92s (contended host, load ~11). Write-up with all Part C numbers: `docs/research/11-design-review/2026-08-27-prelude-build-spike.md`. |
| 2026-08-27 | retrieval | see this lane's detail above |
| 2026-08-27 | `abb9cb9d9` | `statement_goal_record` module: typed bridge from a completed statement-only import to the ledger-shaped fields (kernel-rendered goal, ADR-0350 content identity, substituted-theorem list). Admits nothing to any kernel. |
| 2026-08-27 | `ec8e0f5ec` | Worked-example CLI + integration tests, including a new `TrustedDeclaration` shape (theorem reached only through an auxiliary admitted `Definition`, mirroring the real `Nat.gcd -> Nat.mod_lt` blocker) and a by-hand mutation test on the fail-closed guard. |
| 2026-08-26 | `f1fb56564` | Compose a held-out-safe three-lemma retrieval spine and admit Mathlib's real `Nat.choose_symm_of_eq_add` axiom-free, moving natural binomial from one to two accepted siblings. |
| 2026-08-26 | `dc1a92029` | Restore the complete producer-search checkpoint after a failed induction alternative; preserve the eight-binder contract while replacing two false budget declines with their real missing-composition obstruction. |
| 2026-08-26 | `963977dde` | Falsify the supposed lean4export arrow ceiling with three proof-isolated binomial exports; measure all three under unchanged retrieval and feed the two binder plus one negative-terminal declines into the reusable-family queue. |
| 2026-08-26 | `9e3f1185a` | Join ready facts, measured obstructions, semantic analogues, and operation coverage into a held-out-safe reusable-family queue; natural binomial ranks first with one accepted sibling and two needed. |
| 2026-08-26 | `98628e363` | Replace manual per-fact episode orchestration with a generic frontier-selected authoritative runner that retains crash-safe receipts and permits exactly one machine-selected ledger path to change. |
| 2026-08-26 | `bdfe77340` | One `DEEP_STACK_BYTES` (256 MiB) and one `on_a_deep_stack` replace seven verbatim copies at three unexplained sizes. `examples/kernel_stack_envelope` builds one prelude on an exact stack and answers with its exit status (0/134/2), refusing to run with the prelude cache on because a cache hit type-checks nothing and would report a requirement of ~0. `scripts/check-kernel-stack-envelope.sh` pins the table and halves every budget until the probe FAILS, so a green run has demonstrated it can go red. Six controls; each of the five guards mutation-verified to kill exactly one. |
| 2026-08-25 | `beb27f1ba` | **The trusted-core ceiling, raised the way the gate demanded.** Guard C failed at 5,508 past 5,500 with "say why before raising it." The baseline was RE-DERIVED by `git archive` rather than trusted, giving a per-file table summing to exactly +379 (`tc.rs` +347, `inductive.rs` +30, `env.rs` +2). Verdict: real and necessary — a universe-parameter closure fixing declarations **official Lean 4.30.0 refuses but this kernel wrongly admitted**, and `whnf_core` memoisation (138× cost, 1,857 s → 13.4 s) inside `def_eq`. Ceiling 5,900 with headroom matching the original's character; guard C re-verified to fire by injecting 500 lines in a scratch copy. The file's own comment said "5,110" where the real baseline was 5,129 — wrong from day one. |
| 2026-08-25 | `0f2fb5fcd` | A doc line beginning with `+` is a Markdown list bullet, so ten `doc_list_item` errors pointed at ordinary prose one line below the cause. |
| 2026-08-25 | `6de1d88f8` | Salvage: **the irrationality of √2** (`Nat.no_rational_sqrt_two`) and **`CReal.geom_tail_within`**, committed on behalf of two lanes killed mid-run by a spend limit. Both verified here: 695 tests, clippy `--all-targets`, axiom-free. |
| 2026-08-25 | `03385d2f7` | **`CReal.monotone_of_nonneg_deriv`** — global from local, constructively, no MVT. Four lanes. The congruence is needed at BOTH endpoints, not just the one the handoff named. |
| 2026-08-25 | `dd1ba4808` | `clippy --all-targets` was red on `main` in a doc comment I wrote; four lanes each reported it and each routed around it to the narrower `--lib --tests`. |
| 2026-08-25 | `9703044b7` | `perfect.rs` shipped unformatted behind a green clippy and a green 679-test sweep; `hooks/pre-push`'s `cargo fmt --all --check` caught it. `--lib` structurally cannot. |
| 2026-08-25 | `4a21cbde7` | Correction to a correction: `Int.prodRange_permute` is full-range (`MapsInto σ n`), so the predicate-scoped primitive genuinely does not exist over any carrier. Production regen 1125 → 1141. |
| 2026-08-25 | `af8340e16` | Held-out contamination and the seven-lane fold finding, recorded. |
| 2026-08-25 | `8aa57e4e8` | The `CReal.sqrt` route: `KRegular` at `c = 3` **uniformly in `x`**, so `sqrt` is total and needs no `PosBound` — which a constructive setting could not have supplied, since `0 ≤ x` is undecidable. |
| 2026-08-25 | `be0c67f67` | mobility summary names the dominant unevaluable reason (`unevaluable_no_export`, `unevaluable_top`), so `unevaluable=186` reads as a reachability block not a tactic gap; regenerates the committed census (191->189) that had drifted stale |
| 2026-08-25 | `e27140275` | `--reachable-first`: stably reorder `--next` selection so facts with a frozen export come first (the first 5 eligible had 0); deterministic, population unchanged |
| 2026-08-25 | `b2813872f` | `--skip-unreachable`: preflight the frozen export before spending a model; skips retrieval-miss-only facts at zero cost (~26k tokens/fact saved), opt-in so replays are unchanged; 3 controls |
| 2026-08-25 | `2a2e863f2` | `gen-statement-adapters.py`: proof-free Lean statement adapters from `formal.statement` to expand frozen-export coverage; `--exportable-only` drops arrow-bearing statements lean4export 3.1.0 refuses; verified end to end on s5; 7 controls |
| 2026-08-24 | `da1701d97` | The knowledge overlay may not name a sibling repository: source, namespace, 24 links and three unreachable relation types removed; schema tightened so the vocabulary cannot come back; the validator no longer reads `ROOT.parent`. |
| 2026-08-24 | `94f3beb0c` | The crosswalk and the tactic catalog, plus the two projections that went structurally empty with them. `uses_technique` no longer mandates an external source on every tactic. 13 tactic guards, each killed by exactly one test. |
| 2026-08-24 | `70aaccb38` | `scripts/check-external-coupling.py` — 4 rules, 8 guards, 25 controls, each guard killed by exactly one test; wired into both aggregates with `--self-test` first. `graph_pin` and `resolved` removed from all 104 claims; the 777-line Python integration and the agent's `file://` allowlist entry deleted. |
| 2026-08-24 | `c0c2b6fea` | **ADR-0546 + the gate wired into both aggregates.** Records three findings against the brief: `technique`/`concept` are NOT uninstantiated overlay kinds (24 endpoints, resolved `external-pinned` next door); the existing vocabulary still does not suffice, because `unlocks` is reachability and every `formalizes` edge is *required* to be `completeness: partial` so two cannot compose into "same"; and the motivating `Int.fib_cassini ↔ Rat.det2_mul` edge **is not landable** — neither theorem has a fact and neither is in the kernel projection, so `specialization` ships as a declared kind with zero instances and the gate prints that zero. |
| 2026-08-24 | `06b41a5e6` | **`artifacts/correspondences/` — two theorems can be said to be the same idea, and the claim is checked.** Refuses any pair the ledger's *transitive* `depends_on` closure connects (`F:ml430-nat-fib-add-two` / `F:ml430-int-fib-add-two` is a real such pair and the control pins the refusal against the committed ledger). `carrier-transport` is checked *structurally* — erasing the carrier from both formal statements must leave the same string, and an unknown carrier FAILS rather than skipping. Two status axes mirroring the ledger's, each backed: `asserted` ⟺ empty `via`; `route-recorded` requires every non-null ref to resolve; `mechanized-here` forbids a null ref and requires a checker command; evidence at all requires `mechanized-here`. Empty population exits 1. Prose floors set from measuring `../math-education` (1,263 reasons, median 190 chars — and a bridge to `C:pi` whose reason was about *density* validated cleanly there, which is why nothing here rests on prose). |
| 2026-08-24 | `3ba9c1ec6` | Additive Autogenesis knowledge overlay v1 defines typed, qualified, provenance-bearing links across facts, operations, capabilities, and a pinned read-only external concept graph, with eight seed links and four negative controls |
| 2026-08-24 | `b42ecfd81` | Complete F1's evidence-backed multi-target-producer crosswalk, publish a generated coverage census, and reject uncredited producer or individual complete-coverage claims |
| 2026-08-24 | `137fef720` | Generate the complete constructed-kernel declaration/dependency projection with exact theorem-edge agreement and negative controls |
| 2026-08-24 | `00cbed24b` | Normalize retained decline records into a generated obstruction projection that rejects lost blockers and invented resolution claims |
| 2026-08-24 | `c49566743` | Derive hash-bound transport chains with incomplete paths explicit rather than name-matched |
| 2026-08-24 | `8e78d8e3e` | Publish separated formal, producer-credit, and transport coverage dimensions |
| 2026-08-24 | `7160fc0bc` | Publish non-authoritative producer observations; current live queue has zero registered admissible candidates |
| 2026-08-22 | (pending) | Corrected-checker `Nat.fib_eq_zero` transaction is frozen from clean commit `39b408e619f2` before one crash-safe intent fault and one recovery |
| 2026-08-22 | (pending) | Exit-75 intent fault leaves `Nat.fib_eq_zero` unchanged; recovery performs exactly one ledger write, the registered checker passes, and the measured readiness delta is empty as preregistered |
| 2026-08-22 | (pending) | Replay preflight declines before mutation because current checker-text gate scanning differs from the retained frontier; exact registration commit reproduces the retained frontier byte-for-byte and is frozen as the V2 replay source |
| 2026-08-22 | (pending) | Historical-source preflight correctly rejects its still-open fact; V3 freezes the exact detached transition child, which preserves the registration gate surface and recovered post-state required by replay verification |
| 2026-08-22 | (pending) | Isolated replay `b63854f8…bfaa0` independently repeats `Nat.fib_eq_zero` selection, certified execution, exit-75 recovery, one write, and the exact empty readiness delta |
| 2026-08-21 | (pending) | All 35 dominance audits re-run at `496288979` from a `lane-snapshot` tree; `dominant_unsat` 262 / 324 → **269 / 326**, `lean-reconstruction-gap` 15 → **10**, certified/checked 278 → 280. Four rows moved: QF_NRA cvc5 (+3, `RealProduct`×2 + `MonomialBound`), QF_S (+2, `StringLength`), QF_NRA synthetic (+2, the prelude-warm instrument fix, proved by an A/B with the warm suppressed at two revisions), QF_SEQ (a `parse-error` became `sat`, no dominance change). `gen-proof-gap-matrix`, `gen-proof-gap-shape-census`, `gen-dominance-scoreboard` and `gen-autogenesis-baseline` regenerated; the six moved markers in `PROJECT-STATE.md` and the gap analysis renumbered **with** the account of what moved them, and the ten remaining Lean-reconstruction gaps recorded one line each with the fragment's own decline reason rather than the fallback route's. |
| 2026-08-21 | `a3799dca2` | **`QF_FP/fp_misc`'s "timeout" was an unmemoized DAG walk in the classifier.** `array_bv_abs::abstract_term` re-explored shared subterms once per path; 8/8 `gdb` samples sat in it. Memo + visit budget, each guard mutation-verified to kill exactly one test: **124.7 s timeout → 314 ms**, 4,194,309 visits → 4,365 over 5,762 nodes. QF_FP `timeouts 1 → 0`, certified/checked 15/16 → **16/16**; `dominant` stays 15/16 and the row now declares `bit-blast` instead of `timeout`, because `887b52e64` withdrew its term-level FP route on purpose. Also measured and pinned: `QF_BVFP/Float-no-simp3-main` is not the "evidence exceeds 120 s" it was recorded as — its reduction certificate is `proved` in **28.3 ms** and is withheld only by `produce_evidence`'s blanket "timeout set → skip", whose deadline covers the SAT search and none of `lower_terms` / `tseitin_encode` / `check_drat` / LRAT. QF_FP and QF_BVFP audits re-run at `a3799dca2`; `proof_errors` 4 → **3**, certified/checked 280 → **281**, and the four moved markers in `PROJECT-STATE.md` and the gap analysis renumbered with the account of what moved them. |
| 2026-08-21 | `17079b33d` | `:pattern` was parsed and dropped; the author's trigger now decides. Arena side table, alternatives unioned, multi-patterns joined, declines explicit. ADR-0537. |
| 2026-08-21 | `da314781b` | QF_NIA post-fix: 39/83 = 47.0%, **+6** on its own pre-fix sweep four hours earlier. Which corrects the batch note: `40a1ab969` — one file in `dpll_lia.rs` — moved FOUR divisions (QF_UFLIA +18, QF_NIA +6, QF_SLIA +2, QF_RDL +1), one of them strings and one nonlinear, where it was expected to move QF_UFLIA. Scoped to the expected division, three of those rows would have been recorded at PRE-FIX values under today's date with the freshness gate green over them. |
| 2026-08-21 | `f2060eeb2` | The freshness gate runs in hosted CI too — the third place the gap analysis named. Held back deliberately until the board was green, because a gate that reds CI on landing over a multi-hour sweep is one people learn to override. Runs in the `fetch-depth: 0` job, which is load-bearing: the solver-currency column needs history and degrades to NO-GIT on a shallow clone (verified against a `.git`-less tree — reports NO-GIT, still exits 0). |
| 2026-08-21 | `45587c513` | QF_NIA gap #4 diagnosed. "Multi-year catch-up" confirmed for the search — three cheapest levers yield 0 / +1 / +3 files, 4× clock buys 0 of 20 timeouts — and three premises corrected: **cvc5 is on this host** (`/nas3/data/axeyum/harness/bin/cvc5`, not on `$PATH`; two docs say otherwise), **z3 is 60 files from cvc5 here** (136 vs 76, cvc5's set a strict subset), and **the deficit is one family** (`VeryMax/ITS` = 74 of 104 misses; excluding it, 74.4 % of cvc5). `int-blast-ladder` decisive on 158/161; its constant-fit rule leaves **1 live rung on 32 files, 0 decided**. Four per-file passes committed. |
| 2026-08-21 | `b3ef9a965` | The refusal census picked the next thing to build, and it was not what the gap felt like. `(get-model)` declined 66 times over 400 corpus files and **58 were arrays**, against 6 uninterpreted-sort tokens; arrays now render as `(store … ((as const (Array I E)) default) …)` and the same census reads **166 rendered, 9 refused**. Also `DecidedQuery::proof_eligible`: a bounded-string `unsat` the gate did not confirm cannot draw an Alethe proof of the *packed* assertions. That one is defence in depth and says so — over 184 QF_S/QF_SLIA benchmarks, deleting it changes no answer, because the QF_BV emitter declines those shapes. |
| 2026-08-21 | `81361cdd1` | Gap #3's items 2–4. `solve_smtlib_session` answers `get-model`, `get-value`, `get-unsat-core`, `get-proof`, `get-assertions` and `echo` at the command where they stand; `set-option` reports `unsupported` for every option it does not honour; `(set-logic NONSENSE_XYZ)` says `unsupported` and still decides, as z3 does. `solve_smtlib_incremental` became the same walk with the output commands off, so no verdict could move — A/B over all 1,430 tracked `.smt2` at a 10 s budget: 2 differences, both on files that finish in 9.7–11.8 s, both binaries agreeing three of three at 60–120 s. 34 tests; 23 guards deleted one at a time, 22 killed a test and 16 killed exactly one. |
| 2026-08-21 | `326445bba` | Gap #6: `nra-even-power`, `finite-array-extensionality` and `finite-domain-pigeonhole` no longer checked by re-running their producer — 11 guards, 11 satisfiable-query fixtures, each deletion killing exactly one test. All 28 remaining re-run checkers classified: **16 instances are a complete decision procedure re-run, not the defect**; 14 across 5 families cannot be made independent without a certificate change and are now named in the code. |
| 2026-08-21 | `3a509de54` | Carcara HAS array rules: `check_alethe` gains `arrays_idx`/`arrays_row` under Carcara's semantics, `prove_qf_abv_unsat_alethe` emits `arrays_idx` instead of a name Carcara rejects, and `portable_artifact` decides Alethe portability from the artifact's rule vocabulary rather than its variant. Six guards, each deletion killing exactly one test. |
| 2026-08-21 | `4b0f001c7` | Built Carcara for the first time and ran the crosscheck suite: **5 of 79 tests failed**. Four hand-wrote stale `!fn_app_*` ids into the problem (fixed by reading them from the proof); the fifth found `bv_poly_simp` checked by neither checker. Adds the shipped ROW-same proof's Carcara acceptance, its negative control, and tamper rejection in both checkers. |
| 2026-08-21 | `f9ccdcb9d` | `alethe_portability_probe`: the first committed tool behind the "externally checkable" figure, plus the per-`ArrayAxiomKind` census showing the array-axiom family unreachable at every rung and why. |
| 2026-08-21 | `40a1ab969` | `crates/axeyum-solver/src/dpll_lia.rs` + ADR-0538 + `bench-results/lia-core-minimisation-20260821/`: theory-core minimisation rationed by an oracle-call work budget instead of a core-width gate. QF_UFLIA 92 → 114 (+22, −0) at 0 disagreements against z3 and 0 against the declared `:status`. |
| 2026-08-21 | (pending) | `docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md` + `bench-results/linear-arithmetic-diagnosis-20260821/`: gap #1 diagnosed — three causes not one, 800-file per-file classification, two A/Bs (one refuted, one +17 QF_UFLIA files at 0 disagreements). |
| 2026-08-21 | `9333f779d` | **`bv_nego` returned a wrong `sat` above 128 bits.** `1u128 << (w - 1)` with legal widths to 65536: Rust masks the shift mod 128, so at `w = 129` the term became `x == 1` instead of `x == 2^128` and the shipped `SatBvBackend` answered **`sat`** to an unsatisfiable query (measured with overflow checks off; debug panicked instead). Fixed by following `bv_umulo`'s existing wide branch. Corpus reachability, which the gap analysis marked UNVERIFIED: **0 of 1430** tracked `.smt2` files use `bvnego` (control: `bvadd` in 106), so it is reachable only from the parser on user input. Three tests close the width asymmetry that hid it — widths 129/130/191/192/193/256/4096 by value *and* by the constant's structure, the 128-bit boundary staying narrow, and the end-to-end backend verdict. Two guards, each mutation-verified to kill exactly one test, registered as `ir-bv-nego-width`. |
| 2026-08-21 | `d4ffe2a54` | **`SolverConfig::memory_limit_mb` was set but never read on the shipped build** — its only read was under `#[cfg(feature = "z3")]`, and `axeyum-verify`'s `tock_log2_external` had been setting a 2 GB cap on a non-z3 build where it bounded nothing. Now two mechanisms: a portable pre-allocation clause ceiling at a **measured** 384 B/clause (peak-RSS, fresh process per width; a plain `VmRSS` delta under-reports 3–7x and `VmHWM` is monotone, so both obvious methods fail toward *under*-charging), and a `/proc/self/status` probe (**9.4 µs**, 276x an `Instant::now()`, which is why it may only sit at a phase boundary) at three BV boundaries and both front doors. Measured against a tree without it: default path indistinguishable (182.8–183.4 vs 184.0–185.3 µs/check), a configured limit **+32 µs/check fixed**. All five guards **SURVIVED** the first mutation run because they shadowed each other; a scripted-RSS test seam plus direct reach to the post-encoding gate now has each killing exactly one test. A *faithful* bound still needs a `#[global_allocator]` hook — process-global, `unsafe impl`, needs per-query attribution — recorded as an open research question rather than an unspoken gap. |
| 2026-08-20 | `9eb81822f` | Isolate persistent pre-push worktree metadata from the caller lane and register the two-sided control |
| 2026-08-20 | `24b16642e` | Confirm the repaired hook against a live Rust push with unchanged caller state and a clean exact-SHA gate checkout |
| 2026-08-20 | (pending) | The string family's first re-derivable UNSAT artifact beyond word-clash/regex-emptiness: `Evidence::UnsatStringLength` abstracts every string term to an integer length keyed on its SOURCE NAME, names the five theory lemmas the argument uses, and closes with one nonnegative combination per case-split branch. The checker is two stages — bind each lemma to the conjunct that licenses it, then re-derive the arithmetic — and is arena-free, because a string script's flat view is the bounded packed-BV encoding rather than the query. 23 guards mutation-checked; two killed nothing and were fixed rather than kept (one was dead code the command allow-list already covered, one had no multi-`check-sat` fixture). Also: `diagnose_evidence` reported the ARENA front door for string files, i.e. a query nobody solves — it now reports the text front door too, and agreed with the dominance audit for the first time. |
| 2026-08-20 | `0797719a7` | Rational operands no longer defeat algebraic field arithmetic; the NRA `sat` witness replays and the evidence route matches the decision route |
| 2026-08-20 | (pending) | `Evidence::UnsatRealHandelman`: multi-term Handelman/Positivstellensatz refutations for `QF_NRA`, with case splitting over a top-level disjunction and polynomial multipliers on asserted equalities. Certifies the three corpus rows `nra_product_cert` declined by design. 15 guards mutation-checked; 14 kill at least one test, and the fifteenth (the producer's own self-check) kills nothing and is documented as such at the function rather than pretended to be a guard. Three checks that provably could not fail were deleted instead of kept. `NamedPoly` is now shared with `nra_product_cert` rather than reimplemented — two name-keyed polynomial types would be two chances to disagree about what `a*b` means. |
| 2026-08-20 | (pending) | `Kernel::whnf_core` is memoised — the second of Lean's two reduction caches (`m_whnf` beside `m_whnf_core`), which this kernel never had. `build_creal_prelude` 33.0 s → 13.0 s, template reuse 0.41 s → 0.15 s. Pure memoisation: same key discipline as the δ-free memo, split on `has_fvars`, cleared by `push`/`pop` and by environment revision, closed half covered by the `reduction_ctx_reads` tripwire. Six guards mutation-checked, each killing at least one test and four killing exactly one; a seventh looked unreachable and a `debug_assert_eq!` proved it is not, which is what the comment on it now records instead of the argument that was wrong. Root cause recorded: `502184d3f` did not slow the kernel down, it switched the literal-`Nat` acceleration ON for the first time, because `build_nat_binop_table` gates on `Bool`'s constructor order. |
| 2026-08-20 | (pending) | `Kernel::reduce_nat_binop` moves out of the δ-free normaliser to Lean's two call sites — `whnf_core`'s δ loop (Lean `whnf`, `type_checker.cpp:670`) and `lazy_delta_step` (Lean `lazy_delta_reduction`, `:978`) — both under Lean's `!has_fvar` guard. `build_creal_prelude` 12.99 s → 6.79 s (median of three interleaved rounds), against 8.71 s before the acceleration was ever switched on. Measured separately: Lean's placement *without* the guard is 12.12 s, so the guard is the entire win and the placement is faithfulness, not speed. Identification unmoved — kernel lib 399/0; full kernel crate 609 passed / 1 failed, the one (`real_lean_wellfounded_elaborator_divergence`) failing byte-identically on an unmodified `HEAD` and being a real-Lean *elaborator* rejection rather than ours; solver `reconstruct::` 312/0; clippy 618/618 targets 0 diagnostics; prelude-reuse differential `compared=8 failures=0`; axiom ledger `axreal=30` and all others 0. Three new tests in `tests/nat_literal_arithmetic.rs` pin both call sites and both guards on an environment where the accelerated answer and the declared body disagree; each guard mutation kills exactly one. ADR-0536. |
| 2026-08-20 | `01d54044a` | **Certified 278/324 (85.8%)**, from 267/327 (81.7%) this morning. Timeouts 10 -> 4, `proof_errors` 10 -> 4. Four of the recovered rows were emitters that had returned the CORRECT answer and were billed 31.9s of shared prelude construction inside a 15s cap; `prelude_warm_ms` is now a visible artifact field instead of one instance's bad luck. |
| 2026-08-20 | `5a25f247a` | **Four DAG walks were exponential today, all the same bug written four times** — `contains_quantifier`, `lower_derived_bv`, `collect_enumerable_symbols_rec` (1.28e10 calls in 90s), `collect_nested_registrations`. `Float-no-simp3-main` >300s -> 19.4ms, `fp_fromsbv` 45s -> 3.8ms. The `certify.rs` memo deliberately does NOT collapse occurrences for the quantified-bit budget: that is a tree-sum, and collapsing it would undercount an exponentially shared quantifier nest and let a query past a budget check it cannot satisfy. |
| 2026-08-20 | `609417c9e` | `MAX_UNARY_TERMS` 4096 → 128: mutating the size guard away aborted the test binary rather than failing a test (cost 1026 overflows the stack; cost 514 renders a 13.2 MB module), so the budget admitted the crash it existed to prevent. Now pinned from both ends. The inequality sign re-check killed nothing and was deleted — positivity is enforced upstream by `checked_refutation` and downstream by both Farkas engines. The hypothesis-count check and the external `infer == False` re-gate also kill nothing and are kept, with the mutation pair that shows what the first one does (removing the equality registration kills 7 tests *through* it; removing both kills 1 and ships a quietly weaker module). New `lean_crosscheck` family `qf_s_string_length`: real Lean 4 accepts both modules, 173/173 in the full sweep. |
| 2026-08-20 | `b495a396e` | The string-length certificate reaches the kernel. `reconstruct_string_length` folds the certificate's own facts into a `False` over the constructed integers; `checked_refutation` is now the single derivation both `check_string_length_refutation` and the reconstruction read, so the exported view cannot drift from the validated one. An asserted **equality** enters as an equality — `LraReconstructCtx` grew `hyp_overrides` so the route mints `a = 0` and derives the `≤` half rather than assuming it, which is the one distinction the certificate's fact table turns on. A single-disjunct `(or A)` declines: the query states the disjunction, not the disjunct. Variables are named after their source (`len_xx`, `code_x`). `Evidence::UnsatStringLength` became a struct variant carrying `lean_module: Option<String>`, re-derived on `check` and never read back; a decline is `None`, not a weaker certificate. No `ProofFragment` variant — `scan_proof_fragment` is arena-based and a string script has no faithful arena. |
| 2026-08-19 | `pending` | `scripts/check-kernel-suites.sh`: the kernel's push-time / real-Lean suite partition, discovered from the source and asserted total; `hooks/pre-push` repointed at the non-Lean half (2,296 s → 80 s warm). Found `real_lean_string_monoid_crosscheck` owned by nothing and mis-formatting its check count; floor 218 → 219. |
| 2026-08-19 | `e3e105cd6` | The local-ci freshness gate is ENFORCING in both `check.sh` and `justfile`, on a `PASS` record (`57af69142-s4.json`, 6656 s, 7561 tests + 179 doctests, no vacuous/unreadable step). Landed report-only the day before because the only record was FAIL; that was the sole blocker. Flip re-tested through the real call site: NO_RECORD / STALE / STEP VACUOUS all red, unmodified green. |
| 2026-08-19 | (pending) | `artifacts/local-ci-runs/57af69142-s4.json`: first all-pass authoritative-gate record (5/5 steps, 7561+179 tests, 6656 s); `check-local-ci-freshness` flipped from `--report-only` to ENFORCING in `scripts/check.sh` and `justfile`. |
| 2026-08-19 | `ae0676aec` | `docs/formalized-math-2026-08/` corrected against measurement: "system-proved theorems = zero" falsified (3 facts, re-derived, heavily qualified; C2 still zero); C1 landed 2026-08-14 and did **not** deliver `N x 149/day`, so the single-file-lock diagnosis is falsified by its own remedy; the rate metric retired as unmeasurable across preludes; ADR-0517/0518's two-checker finding and the 122-declaration coverage hole recorded, with the limitation stated at its true width (shipped artefact does not carry the whole carrier; 4 declarations kernel- but not elaborator-checkable). |
| 2026-08-19 | `4c7af898d` | **ℝ is a lattice.** 15 `Rat` + 18 `CReal` declarations, every one accepted on first submission, all footprint-free. The predicted obstacle — a four-way sign split over `|a| − |b| ≤ |a − b|` — never appears. Nothing here has a side condition, so the failure mode is a *degenerate operation*, not a vacuous guard: `max x y := x` satisfies `le_max_left` by reflexivity and `abs x := x` satisfies `le_abs_self`, `neg_le_abs` and `abs_le`. So `not_le_zero_neg_one` and `not_equiv_abs_neg_one` are proved from the laws alone, the witness's exit status depends on both, and `max x x ≈ x` / `max 0 1 ≉ 0` / `min 0 1 ≉ 1` are admitted **through the kernel**. One level down, `Rat.max`/`Rat.min` are checked to COMPUTE on both branches with the wrong answer REFUSED — the nine `ℚ` laws are all one-sided and would hold of a projection. Three one-token mutations refused. |
| 2026-08-19 | `e9f5cf287` | **The mathematics strand stops advising against work that is finished.** `02` gains a dated ℝ/ℂ status block, a `ℂ` row and a corrected `ℝ` row in the construction-order table, measured prelude counts, and a "not built" table with reused costings (cotransitivity ~400 lines, `apart_mul` ~300, completeness/`sqrt`/suprema uncosted, ℂ `abs` downstream of both). `05`'s D3 is re-ordered rather than deleted: it was a pre-flight check on a construction order that has since been walked, and is now a coverage measurement against Mathlib. `04` closes R4 and keeps the 30 `Real` axioms as the ADR-0509 negative control. `01`, `03`, `README` and `diary-real-keystone.md` corrected in place. |
| 2026-08-19 | `c26e492b1` | **The axiomatized reals are renamed `AxReal` (ADR-0522 step 1), and two green assertions were reading the wrong carrier.** `CReal` contains `Real`: a front-door test asserting `contains("Real.add_le_add")` was satisfied by `CReal.add_le_add`, and `infeasibility_farkas_lean`'s ordered-field scan by `CReal.le` — the latter is a `proved` fact's checker command. One string literal moves the whole 30-row package. `--accept-rename OLD=NEW` is new: routing a rename through `--accept-population-change` would have published 30 retirements that never happened. |
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

The accepted library programme below is the new cross-cutting focus. It does
not erase the retained A1–A11 solver programme: P0 safety work
preempts it, P1 graph/artifact authority may run beside A5/A6, and production
pilots begin only after their authorities land. A3 remains incomplete but
yielded, A4 yielded, and A5 remains the first active solver-depth item.

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

Detail moved to [`../notes/112-prelude-perf.md`](docs/plan/notes/112-prelude-perf.md).

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

Detail moved to [`../notes/113-nat-rule-placement.md`](docs/plan/notes/113-nat-rule-placement.md).

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

Detail moved to [`../notes/114-audit-refresh.md`](docs/plan/notes/114-audit-refresh.md).

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

Detail moved to [`../notes/115-fp-misc-hang.md`](docs/plan/notes/115-fp-misc-hang.md).

**Gap #7 closed for `:pattern`, declined for `:weight` (`DONE`,
agent-quantifier-triggers, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 7. `:pattern`
was parsed and dropped; it is now threaded parse → IR → the E-matching loop and
a usable annotation **replaces** auto-selection ([ADR-0537](docs/research/09-decisions/adr-0537-user-triggers-are-a-hint-channel-on-the-arena-and-replace-auto-selection.md)).
Alternatives are unioned, multi-patterns joined, and everything the matcher
cannot fire is declined whole and falls back to auto-selection.

The measurement that motivated it, z3 4.13.3 with its own fallbacks off
(`smt.mbqi=false smt.auto_config=false`): `unsat` unannotated, `unknown` with
`:pattern ((h x))`. Axeyum answered `unsat` for both, in both configurations.

Two findings worth carrying forward rather than re-deriving:

- **The corpus cannot measure this.** 0 of 1430 tracked `.smt2` files contain
  `:pattern` and 0 contain `:weight` (positive control, same command: `assert`
  1419, `forall` 82). The capability delta is zero by construction, and any
  claim about this feature's value has to say so.
- **A verdict is a blunt instrument for "was the trigger obeyed".** Honouring a
  useless trigger did *not* cost the refutation through the front door: term
  invention seeds ground instances of the trigger itself and reaches the witness
  anyway, where z3 with mbqi off has no analogue. The tests measure the proposed
  *instance set* instead.

Next, if this is picked up again: `:weight` needs a corpus that moves under it
before the flood-control cost function is touched (ADR-0537 §5); and the parser
declines any trigger outside an application tree over declared uninterpreted
functions, which rules out arithmetic subterms — the first real workload with
`(f (+ x 1))` as a pattern will want that.

**The parity ledger has a gate, it is ENFORCING in both aggregate gate sets, and
the board behind it has been re-measured** (`WIP`, agent-parity-gate,
2026-08-21). `bench-results/PARITY.md` is the declared headline — external list
pinned by sha256 before each run, `DISAGREEMENTS > 0` voids an entry — and
`scripts/parity-run.sh`, the only thing that writes it, was invoked by **no
gate**: not `just check`, not `scripts/check.sh`, not CI. So the board froze on
2026-08-06 for fifteen days, through UF 32 → 85 and QF_RDL 10 → 105, and nothing
went red.

`scripts/check-parity-freshness.py` derives a per-logic as-of date from each
entry's own header and fails past **14 days** (warn at 10). 14 is not a round
number: any budget ≥ 15 days would have sat green through the whole episode the
gate exists for, and below it the binding constraint is cost — the ledger's own
2026-08-06 sequence puts a division at 68–170 minutes. The budget is **per
logic**, so a red costs one sweep, not a board refresh. The population comes
from the append-only ledger, never from `bench-results/parity-lists/`: a list
can be deleted, so anchoring there would let a logic be dropped from the tracked
set to go green.

Detail and older landed rows moved to [`../notes/117-parity-freshness.md`](docs/plan/notes/117-parity-freshness.md).

**The data coupling to `../math-education` is removed and
`scripts/check-external-coupling.py` refuses its return** (`WIP`,
agent-decouple-math-education, 2026-08-24). The owner's constraint is that the
sibling is REFERENCE ONLY — read it for calibration, never depend on it,
integrate with it, or point at it in data. It was stated and never gated, and by
today it had been violated in **five places at once**, with every validator
involved exiting 0:

- the knowledge overlay (an `external-repository` source, an `external-pinned`
  namespace, **24 of 33 links** pinned to that repo's SHA);
- the family-concept crosswalk (`path_hint: ../math-education/graph/concepts`,
  and a validator that hardcoded the SHA and *required* the file to match);
- `tactic-catalog.schema.json`, where `uses_technique` is required on every
  tactic and required `source: {const: "math-education"}` plus a `revision` —
  so no tactic could be declared here without naming that checkout;
- **all 104 claims**, each carrying `provenance.graph_pin` and 438
  `resolved: true` refs, with the schema making `concept_refs` mandatory and
  `graph` a one-value enum;
- `python/axeyum/knowledge/math_education.py`, 777 lines that resolved
  `Path("..") / "math-education"`, ran `git rev-parse HEAD` against it, and put
  the resulting `file://` prefix **into the agent's fetch allowlist**.

Four validators reached outside the checkout in code, one of them defaulting to
`~/projects/personal/math-education/graph` — an absolute path into one machine's
home directory, in a tracked file.

Detail moved to [`../notes/118-external-coupling.md`](docs/plan/notes/118-external-coupling.md).

**Gap #4 diagnosed; "multi-year catch-up" confirmed for the search, and the
sizing corrected three ways (`DONE`, agent-nia-diagnosis, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 4 →
[nia-deficit-diagnosis](docs/research/05-algorithms/nia-deficit-diagnosis-2026-08-21.md).
Measured at `cb4a391c9` over the pinned 200-file list (sha256 `19b334d3b910`,
the hash in the `PARITY.md` entry), three solvers per file at 24 s.

The framing survives: the three cheapest levers in the division yield **0**,
**+1** and **+3** files, and 4× the wall clock buys **0 of 20** search timeouts.
Ranking QF_NIA last among decision work is right. Three premises around it do
not survive:

- **cvc5 1.3.4 is on this host** at `/nas3/data/axeyum/harness/bin/cvc5` — not on
  `$PATH`, which is why two documents record it as absent. It was reachable the
  whole time.
- **z3 is not a stand-in for cvc5 outside the linear divisions.** Same run:
  z3 **136/200**, cvc5 **76/200**, and cvc5's decided set is a strict *subset* of
  z3's. Row 1's "within 5 files" check is true where it was made and does not
  transfer. So "38.2 % of the reference" means plain cvc5; against z3, 27.9 %.
- **The deficit is one benchmark family.** `20170427-VeryMax/ITS` is 134 of the
  200 files and **74 of the 104 misses**. Excluding it: 29/39 = **74.4 % of
  cvc5**, around QF_RDL. On `20220315-MathProblems` we decide **6 of 9 and both
  references decide 0**.

Mechanism, and it rhymes with row 1's §3.2: every specialised nonlinear-integer
route declines, so `int-blast-ladder` — a *generic* bounded integer bit-blast —
is decisive on **158 of 161** undecided files. Its width ladder admits a rung
only if every integer **literal** fits, so a `2^30` Farkas coefficient kills 14
of 15 rungs. **32 files have one live rung and we decide zero of them.**

Two findings worth not re-deriving:

Detail moved to [`../notes/118-nia-diagnosis.md`](docs/plan/notes/118-nia-diagnosis.md).

**Gap #3 of the 2026-08-21 capability audit is closed at the command level**
(`WIP`, agent-consumer-interface, 2026-08-21). §6.3 ranked the consumer
interface third by measured cost and called it "the difference between a library
and a solver a stranger can run". Four of its six items were one defect wearing
four hats: **the front door accepted a command and did not answer it.**
`get-model`, `get-value`, `get-unsat-core` and `get-proof` were CLI no-ops with
Rust-API-only counterparts; `set-option` was inert; `set-logic` was stored and
never read.

The half landed earlier — `examples/axeyum_cli.rs`, one verdict per `check-sat` —
made the rest sharper rather than softer. A driver that answers `check-sat` and
drops `(get-model)` produces **no output and no complaint**, and that is
indistinguishable from a solver with no model. It is this repository's own
recurring failure: silence read as a negative result.

Detail moved to [`../notes/119-consumer-interface.md`](docs/plan/notes/119-consumer-interface.md).

**Gap #6, second and third turns: three more families converted, and the row's
own denominator corrected (`WIP`, agent-checker-independence, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 6 / §6.2.

`nra-even-power` (10 certified `unsat`), `finite-array-extensionality` (4) and
`finite-domain-pigeonhole` (3) no longer rest on
`producer(arena, assertions).is_some_and(|fresh| fresh == *cert)`. Each is now
decided from the certificate and the query, with **no fall-through** to the
re-run — the lesson from the array-axiom turn, where the same guards placed in
front of the equality comparison killed nothing because the comparison subsumed
them. Eleven guards, eleven adversarial fixtures over **satisfiable** queries,
each deletion killing exactly one test.

**The row's headline number is wrong in our favour, and that is the more useful
finding.** "~30 of 34 checkers re-run the producer" counts one shape and three
situations. All 28 remaining were read:

Detail moved to [`../notes/120-checker-independence.md`](docs/plan/notes/120-checker-independence.md).

**Gap #5: the rule vocabulary was fixed and it was never the binding constraint
(`WIP`, agent-portable-evidence, 2026-08-21).**
[Gap analysis](docs/plan/gap-analysis-smt-solvers-2026-08-21.md) §9 row 5 / §6.2.

**Carcara was built here for the first time.** No host in this repository had a
Carcara binary — not in `references/`, not on `$PATH`, not on any fleet host —
so every test in `tests/carcara_crosscheck.rs` had been passing by returning
early for as long as the file has existed. `references/carcara` now carries a
built `target/release/carcara` (Carcara 1.1.0, `6624ea80`). Building it needs
`m4`, which is not installed on this box but ships inside a snap
(`/snap/gnome-46-2404/153/usr/bin/m4`); no host package was installed.

**The central claim of the array-proof design note is false.**
`docs/research/07-verification/array-elimination-alethe-proofs.md` records
"Alethe/Carcara has NO array theory rules", quoted from there into six doc
comments, into `check_alethe`'s dispatch, and into the design of two emitters.
Carcara 1.1.0 registers `arrays_idx`, `arrays_row`, `arrays_row_contra` and
`arrays_ext`, and `arrays_idx` **is** axeyum's `read_over_write_same`, shape for
shape. Same problem, same proof, one identifier changed:
`read_over_write_same` → `unknown rule` / `invalid`; `arrays_idx` → `valid`.

Detail moved to [`../notes/121-portable-evidence.md`](docs/plan/notes/121-portable-evidence.md).

**The GF(2) machinery is on `main`; the Kaser--Lemire attack is not** (`landed`,
lemire-integration, 2026-08-23, ADR-0544, `b99d715bc`). Two lanes had produced
~1.3 M lines across four artifacts, and neither was mergeable whole: `main` was
57 commits ahead and **694 behind** origin, and `agent/gf2/lemire-proof` carried
the entire attack alongside the machinery.

Three things this cost, worth carrying forward:

**Sixty ADR numbers were double-allocated and `git merge-tree` reported no
conflict on any of them.** The branch allocated `adr-0484`--`0592` while
`origin/main` independently allocated `0484`--`0543`; the *filenames* differ, so
both sets merge clean and land side by side under one numbering. The generated
index would then render two different decisions as one sequence. A clean
`merge-tree` is evidence about content, not about a shared namespace — and this
repository has two such namespaces (ADR numbers, fact ids) that no merge check
covers.

**A module's size is not evidence that it is load-bearing.** `gf2_hayes.rs` is
26,655 lines and 266 public items, the largest module in `axeyum-cas`, and it is
a leaf: it imports nothing from the rest of the crate, and the only inbound
references from the keep-set were six in `gf2_extension.rs`, every one a doc
comment or `#[cfg(test)]`. The extraction that looked infeasible was four test
assertions.

**Grepping the module path missed a coupling that only failed at link time.**
`tests/gf2_artifact_cli.rs` reports clean for `gf2_hayes` and still reaches it,
through `env!("CARGO_BIN_EXE_axeyum-gf2-hayes-conditional-variance")`. When
cutting a module out of a crate the coverage surface is module paths **and**
`CARGO_BIN_EXE_*` names **and** `Cargo.toml` target declarations; a clean grep
over the first says nothing about the other two.

Which facts stayed was decided mechanically rather than editorially: a fact stays
iff every `evidence.artifact` it cites resolves under a retained path and no
checker command reaches `gf2_hayes` or `artifacts/gf2`. Exactly four of 45
qualify, `depends_on`-closed. The other 41 would have left the ledger asserting
evidence this repository can no longer produce.

Detail moved to [`../notes/122-lemire-integration.md`](docs/plan/notes/122-lemire-integration.md).

**Theorem correspondences (`WIP`, agent-correspondence-model, 2026-08-24).** The
data model can now state that two settled facts are the same mathematical
content, and cannot state it where `depends_on` belongs
([ADR-0546](docs/research/09-decisions/adr-0546-theorem-correspondences-are-not-proof-dependencies.md)).
`artifacts/correspondences/*.json`, one file per adjudication on the
`artifacts/facts/` pattern, gated by `scripts/validate-correspondences.py`
(`just correspondences`; 39 mutations, 39 killed, one test each). Three
instances landed, all `route-recorded`.

Detail moved to [`../notes/123-theorem-correspondences.md`](docs/plan/notes/123-theorem-correspondences.md).

**Curriculum-directed kernel development (`WIP`, coordinator, 2026-08-25).**
**1,106 distinct theorems, every one axiom-free**; trusted base unmoved at 30
declared-and-unreached `axreal` assumptions, and no `Opaque` or `Quotient`
declaration exists anywhere, so `Axiom`-only and the trusted surface coincide. Fact ledger **362 → 587**, `missing_edges=0`.

**The loop is code-complete.** Frontier selects → operation re-derives → receipt
survives a re-signed cross-target forgery → transaction verifies. Reproduced
end to end; the fact stays `open` on purpose, because whether to WRITE is not a
decision a gate should make.

**Why it is not yet automatic has a measured answer, not a direction.** Three
producers cover 7, 4 and 1 facts; the third is single-target **by
construction** (`const TARGET`, `const STREAM_SHA256`). Both routes past the
wall were tested: premise composition dies on WHNF opacity — reconfirmed
through a code path that never touches the induction producer — and on a
`fibAux`-vs-`Nat.iterate` representation mismatch; iterate re-derivation dies
because `LE.le` desugars to a four-argument spine and is rejected before any
combinator runs. The next capability is named: an order-relation combinator
vocabulary. Full chain in doc 262's fourth, fifth and sixth amendments.

**Next.** (1) That vocabulary, narrowly scoped — the previously-reverted broad
version exhausted a shared budget for zero admits. (2) Coverage is 210+/1134;
`Complex` and `CPoint` are thinnest. (3) `sumRange_cauchy_of_dominated` is three
named steps from closing.

**Three findings outrank the counts.** The binding constraint on the mathematics
is a **missing type** — no `List`, no `Finset`, no product — found every time by
a lane trying to prove something, never by planning. **Three targets I named
were false or unsatisfiable**, and lanes refuted them with counterexamples
rather than failing to prove them. And **reading a producer gave a plausible,
partly wrong picture three times running**; every correction came from running
it.

**A day of parallel mathematical development against the kernel, 3–5 lanes
throughout** (`DONE`, flywheel-mathematics, 2026-08-25). Production moved
**1,096 → 1,175 distinct theorems, all axiom-free, 0 axiom-bearing**; the
trusted base did not move (30, all `axreal`, none reached by any shipped route).
Kernel `--lib` sweep 656 → 695 green. Full write-up:
[`../../mathematics-2026-08/diary-flywheel-2026-08-25.md`](docs/mathematics-2026-08/diary-flywheel-2026-08-25.md).

The theorems are the smaller half of the output. **Three structural findings
came from lanes failing to prove things and reporting why**, and none of them
was visible from any plan:

Detail moved to [`../notes/125-flywheel-mathematics.md`](docs/plan/notes/125-flywheel-mathematics.md).

**Turn the architecture review into executable product increments** (`WIP`,
top-three-focus, 2026-08-25). The durable plan is
[`../../top-three-focus-plan-2026-08.md`](docs/top-three-focus-plan-2026-08.md);
the full lane history is in
[`../notes/126-top-three-focus.md`](docs/plan/notes/126-top-three-focus.md).

Detail and older landed rows moved to [`../notes/126-top-three-focus.md`](docs/plan/notes/126-top-three-focus.md).

**WIP, open-problems-programme, 2026-08-26.** Five durable research packages now own the
Rado/Schur, GF(2) bilinear-rank, S-box optimality, SIMD-shuffle minimality, and optimization
bound-certification targets.  The Axeyum-side programme contract is
`docs/research/10-cas/open-problems-programme-2026-08.md`: pin current literature status,
generate deterministically, run untrusted search, independently replay/check, bind evidence,
and reconstruct formal identities into the kernel where applicable. Current focus stays on
`abz7`: deterministic detectable-precedence closure is complete and exhausted after one round,
and an exact checker-compatible FlatZinc/DRCP route is calibrated against both an independent
Rust checker and the Rocq-verified FznDrcpCheck. Sustained `abz7@655` proof production remains
live without a short wall-clock cutoff; the upper-bound search is closed by the replayed public
656 witness described below. The
settled-cell calibration is green for `R_3(x-y=z)=14` (42 variables,
356 clauses, 25 checked DRAT steps); a mutated DIMACS header fails closed, and the aggregate
claim sweep reports 104 claims re-checked / 0 errors / 25 rows explicitly not re-checked.
The SIMD brief's named byte-reversal target is now closed in its explicitly listed fixed
shuffle set; the other four headline targets remain open.

**S-box top-level semantic cell 8 checked, 2026-08-27.** The bounded whole-tree checker
accepted all 961 manifest-selected obligations beneath top-level Boolean-product cell 8:
931 leaf DRAT refutations and 30 covering proofs totaling 62,886,514,460 consumed bytes.
Every formula was reconstructed from the hash-bound exact-irredundant base and its typed cube
path; the terminal log and root manifest/cover are hash-bound in the sibling receipt. This
closes one of the 32 exhaustive semantic cells, not the remaining 31 and not the full MC<=7
formula, so the `[7,8]` interval and five-problem scoreboard do not move.

**S-box top-level semantic cell 4 checked, 2026-08-27.** The same bounded checker reached
`385/385` and terminal `unsat-checked`: 373 leaf DRAT refutations plus 12 covering proofs,
57,326,968,062 manifest-selected bytes. The base, typed cube, manifests, cover, checker binary,
terminal log, and counts are hash-bound in the sibling receipt. Cells 4 and 8 now close 2/32
exhaustive semantic cells. The other 30 remain open, so the `[7,8]` interval does not move.

Detail moved to [`../notes/127-open-problems-programme.md`](docs/plan/notes/127-open-problems-programme.md).

**The kernel's stack requirement is now a measured, pinned, gated number, and
the numbers say the margin was zero** (`WIP`, kernel-envelope, 2026-08-26).

The trigger was `CReal.e` making
`every_creal_declaration_is_checked_and_axiom_free` — the single test behind
this project's axiom-freedom claim — SIGABRT instead of run. Exit 134 is
indistinguishable from a broken tool or an absent declaration, and this
repository has read it as both.

Bisected the real requirement (`scripts/check-kernel-stack-envelope.sh
--measure`): the smallest power-of-two thread stack on which each prelude
build completes.

| prelude | debug | release | ratio |
|---|---:|---:|---:|
| `cpoint` | **33,554,432** | 1,048,576 | 32× |
| `complex` | 4,194,304 | 262,144 | 16× |
| `creal` | **2,097,152** | 131,072 | 16× |
| `rat` | 1,048,576 | 131,072 | 8× |

`creal` in debug needs **exactly** the 2 MiB default a spawned thread gets,
which is what a `#[test]` runs on — there was never any margin, and one deep
declaration was always going to end it. `cpoint` needs 32 MiB, so the five
sites using a 64 MiB `on_a_deep_stack` copy had **2×** headroom, not the
comfortable margin the number looks like.

**The recursion-depth limit that was proposed is the wrong instrument, and the
measurements are why** (ADR-0584). Debug frames cost up to 32× release frames
at *identical* depth, so one constant cannot serve both profiles; the two deep
recursions cost ~2,250 B and ~576 B per frame, so depth does not predict stack;
and only `infer_core`/`check_core` return `Result` — `whnf_core`,
`def_eq_core_uncached`, `instantiate_aux` and `abstract_aux` cannot report one.
Lean 4.30's own kernel uses a **stack-pointer probe** with a 128 KiB margin
throwing a catchable `stack_space_exception`; the depth counter arrived only in
4.34, as a supplement. That design is deferred with its open questions written
down, not rejected.

Detail moved to [`../notes/128-kernel-stack-envelope.md`](docs/plan/notes/128-kernel-stack-envelope.md).

**Your lane's block (`DONE`, series-tests, 2026-08-27).** Assessed the
22–23 curriculum row against the theorem inventory before adding anything:
comparison test, dominated convergence, telescoping, and `geomCauchy` were all
already landed and accurately described. **Landed absolute convergence implies
convergence** — `CReal.sumRange_cauchy_of_abs_cauchy` and
`CReal.sumRange_converges_of_abs_converges`, both pure corollaries of the
already-proved `sumRange_cauchy_of_dominated` at `g := abs ∘ f`, kernel-checked
(`creal_prelude_builds`, 17.5s, healthy) and covered by
`every_creal_declaration_is_checked_and_axiom_free`'s environment scan.
Added a soundness-negative control confirming the trusted checker rejects the
reversed (classically false) direction using the real theorem's own proof
value.

Found and corrected two stale curriculum claims: row 22–23's "`CReal.inv`
contained to exactly two declarations" undercounted — the true count along
`geomCauchy`'s dependency chain is **six** (four pre-existing in
`geometric.rs` plus the two in `exponential.rs`); and row 18's "`2 ≤ e ≤ 3`
open" was stale — `CReal.two_le_e`/`CReal.e_le_three`/`CReal.e_le_four` are
already proved. Both corrected in `docs/curriculum/foundational-books/spivak.md`.

Assessed and declined, with reasons sized precisely in the curriculum doc's
new "Postscript III": the **ratio test** (needs a `PosBound`-witnessed
multiplicative form to stay `inv`-free — new construction, not a corollary)
and **`e` irrational** (needs an `n!·e`-integrality argument this development
has no machinery for at all).

Next open goal: build the multiplicative ratio test
(`∀n, le (mul r (f n)) (f (succ n))) → …`, comparison against an `r`-scaled
geometric series) as a genuinely new construction over `geom_sum_bounded`'s
existing shape.

**Your lane's block (`DONE`, ledger-integral, 2026-08-27).** The kernel had
~60 inventory rows matching `riemannSum|CReal.integral` (roughly thirteen
lanes' work this session) and the fact ledger had **zero** — a real negative,
confirmed against a 180-fact `CReal` control. Registered ten new facts
covering the construction and its algebra: `F:creal-riemannsum-cauchy`,
`F:creal-integral`, `F:creal-integral-converges`, `F:creal-integral-const`,
`F:creal-integral-add`, `F:creal-integral-le`, `F:creal-integral-scale`,
`F:creal-integral-witness-independent`, `F:creal-riemannsum-integral-close`,
plus the supporting bridge `F:creal-sharedindextocanonical` (the only one of
the optional bridges with a fully honest `depends_on` — every one of its
three direct dependencies was already a registered fact).

Canonical types and direct dependency edges were read from the kernel via a
standalone probe binary (built in the session scratchpad, deleted after use)
and cross-checked against `theorem_dependency_inventory`'s own output on this
tree. `depends_on` links to existing ledger facts wherever
`theorem_dependency_inventory` names one (most of `riemannSum_cauchy`'s
14-edge dependency set was already registered); unregistered prelude
dependencies (`riemannSum_reblock_close`, `riemannSumDeepCauchyFolded`, the
rest of the `riemannSumDeepCauchy*` family, `common_refinement` — a private,
unregistered Rust helper, not a kernel declaration) are named in each fact's
`notes` rather than registered speculatively.

Detail moved to [`../notes/130-ledger-integral.md`](docs/plan/notes/130-ledger-integral.md).

**Your lane's block (`DONE`, ledger-euler, 2026-08-27).** `CReal.e` had NO
fact, nor did `two_le_e`, `e_le_three`, or `e_le_four` — a real negative,
confirmed by `/usr/bin/grep -rl` across `artifacts/facts/` against a control
that found 180 `CReal` facts. Euler's number was constructed in this kernel
and entirely unrecorded in the product.

**Task 1 — the sibling lane's claimed blocker was real, and it is now
closed.** Eight examples do mention `Declaration::Definition`
(`kernel_declaration_projection.rs` among them), but none took a name and
asserted a `Definition` exists with a non-zero exit on absence —
`theorem_dependency_inventory` / `nat_theorem_inventory` /
`prelude_theorem_inventory` all filter to `Declaration::Theorem` by explicit,
documented contract. Added `--require-declaration <name> [--require-kind
<kind>]` to `kernel_declaration_projection`: it searches every constructed
prelude's environment for an exact display-name match (of the given kind,
when given) and exits non-zero when none is found; unfiltered invocations
(no new flags) are byte-identical to the prior behaviour (verified: 7,278
unfiltered rows, unchanged TSV shape — this is what
`gen-autogenesis-kernel-dependency-projection.py` still consumes).

Detail moved to [`../notes/131-ledger-euler.md`](docs/plan/notes/131-ledger-euler.md).

**Your lane's block (`DONE`, ledger-trig, 2026-08-27).** Registered 28 new
facts in `artifacts/facts/` for mathematics that had been built in this
kernel across four sibling lanes' work (`creal/trig.rs`,
`creal/ratio_test.rs`, `creal/crossing.rs`, `crates/.../src/complex/poly.rs`)
but had no ledger entry.

**Ch.15 (trigonometry, the kernel's first transcendental value):**
`F:creal-cosone` (the CONSTRUCTION, via `CReal.mk` on an explicit regular
sequence, never `Exists`-elimination), `F:creal-costerm`,
`F:creal-cosseriespartial`, `F:creal-costermabsledominant`,
`F:creal-cosoneconverges`, `F:creal-cosone-le-four`,
`F:creal-neg-four-le-cosone`. The last two are recorded as what they are: a
LOOSE, uniform `[-4,4]` bound (no case split, unlike `e_le_three`'s genuine
kink at index 2), reusing `CReal.e`'s domination unchanged and discarding
the alternating series' sign cancellation via the triangle inequality — it
does not pin `cos(1)`'s sign, let alone approximate `cos(1) ~= 0.5403`. Both
facts' `statement` and `notes` say this explicitly.

**Ch.22-23 (series):** `F:creal-geomcauchyoflt`,
`F:creal-geomcauchyofltordered`, `F:creal-geomscaledcauchyoflt`,
`F:creal-sumrangeratiotest`.

Detail moved to [`../notes/132-ledger-trig.md`](docs/plan/notes/132-ledger-trig.md).

**Your lane's block (`DONE`, ledger-uc, 2026-08-27).** Registered 26 new
facts in `artifacts/facts/`. `python3 scripts/validate-facts.py` is green:
**776 facts checked, 0 errors** (750 pre-existing + 26 new).

**Ch.24 (uniform convergence, new chapter):** `F:creal-uniformconvergeson`
(the CARRIER — a one-constructor `Type` in `Sort (1)`, not `Prop`: its
`--require-kind` is `inductive`, not `definition`), `F:creal-uniform-converges-id`,
`F:creal-uniform-converges-geom-half` (the two concrete instances),
`F:creal-uniform-limit-uniformly-continuous` (the headline theorem). Every
fact's `statement` records that `UniformConvergesOn` must be `Type`-valued
because the headline theorem *constructs* a `UniformlyContinuousOn` witness
from the rate as literal `Nat` data, and `Exists.rec` is `Prop`-only. No
pointwise-not-uniform counterexample is claimed or checked; the guarantee is
recorded as a type-level argument (`rate : Nat`, not `CReal -> Nat`).

**Ch.22-23 (alternating series):** `F:creal-negonepowdouble`,
`F:creal-alternatingeleo`, `F:creal-alternatingbracket`. **NOT registered**
(do not exist in the merged tree): `CReal.alternatingBracketUpper`,
`CReal.alternatingLowerBound`, `CReal.alternatingUpperBound` — see Findings
below. *(Since landed — all three now exist in the kernel; historical record.)*
<!-- was-absent: CReal.alternatingBracketUpper, CReal.alternatingLowerBound, CReal.alternatingUpperBound -- this status note's snapshot of the merged tree; all three since landed -->

**Ch.20 (`CReal` polynomials):** `F:creal-polyeval` (+`-zero`/`-succ`),
`F:creal-polyadd`, `F:creal-polyeval-polyadd`, `F:creal-polyscale`,
`F:creal-polyeval-polyscale`, `F:creal-polydegreelt` (recorded as a
PROPOSITION, not a computed degree — `CReal.Equiv`/`CReal.le` are
undecidable) (+`-polyadd`/`-polyscale`).

**Ch.25-27 (`Complex` polynomials, factor theorem):**
`F:complex-polydegreelt-polymul`, `F:complex-hornerfromtop`
(+`-zero`/`-succzero`/`-succsucc`), `F:complex-factorquotient` (a COMPUTED
quotient via a nested `Nat.rec`, never `Exists`-elimination — its own notes
record the forced-`zero`-prepend boundary bug the natural reindexing hits),
`F:complex-factorquotient-degreelt`.

**Ch.14 (integral machinery):** `F:creal-meshscaledleofge`,
`F:creal-crossingclose` — registered as what the theorem STATES, with its
`statement` and `notes` explicit that `hap`/`hpb` (`samplePt`'s domain
membership) are UNDISCHARGED hypotheses of the theorem itself, not a proof
gap; the theorem the kernel admitted is fully and soundly proved but not
usable as a closed result until those two hypotheses are separately
discharged.

Detail moved to [`../notes/133-ledger-uc.md`](docs/plan/notes/133-ledger-uc.md).

**Frontier admissibility diagnosis (`done-for-now`, frontier-fix, 2026-08-27).**
Re-measured doc 262's `fact-frontier.py --json` result on today's 776-fact
ledger: ready 141→132, admissible unchanged at 0. Root-caused it precisely,
against the validator rather than by inference: `validate-autogenesis-
operations.py`'s `ADMISSION_CONTRACTS` is a closed set of exactly two tuples,
both requiring `epistemic_status: "proved"` — so no operation can be
registered for a fact whose proof does not already exist somewhere,
independently checked. Confirmed empirically that all 27 currently-registered
operations name already-proved facts, and that zero orphaned
"candidate-checked-not-admitted" manifests exist for any open fact (nothing
free to wire in). Of 776 facts ledger-wide, exactly one open fact
(`F:fp16-add-monotone-rne`) is in a decidable SMT fragment; the other 125
ready-but-unregistered facts need a genuinely new kernel proof via the
s5-hosted Mathlib/lean4export pipeline. Did not fabricate an operation
claiming `proved` for unproved work — that is the exact "checker that cannot
fail" defect this project repeatedly finds and repairs. Full writeup:
`docs/autogenesis/288-admission-precedes-registration.md`.

**Landed.** A purely additive `diagnostics` key in `fact-frontier.py --json`
(`ready_count`, `admissible_count`, `unregistered_by_route_class`) so the
decidable/proof-route-only/no-route split doesn't have to be reconstructed by
hand every time; 8/8 existing `test_fact_frontier.py` cases still pass
unmodified. No change to `artifacts/autogenesis/operations.json`,
`nursery-v1.json`, or any fact — `check-autogenesis-holdout-isolation.py`
still passes (`held_out=37|verdict=PASS`), confirming the partition is
untouched.

Detail moved to [`../notes/134-frontier-fix.md`](docs/plan/notes/134-frontier-fix.md).

**Your lane's block (`DONE`, ledger-5, 2026-08-27).** Registered 29 new facts
in `artifacts/facts/` (28 `kernel-lean` + 1 `cas-certificate`).
`python3 scripts/validate-facts.py` is green:

```
805 facts checked, 0 errors  (computed=2 conjectured=3 open=176 proved=620 refuted=4)
  routes: cas-certificate=24(kernel-reconstructed=0,cas-internal=24) imported-kernel-lean=5 kernel-lean=559 search-certificate=12 smt-clausal=9 smt-term-level=17; 557 axiom-free on kernel-lean (not comparable across routes)
  cas-certificate: 24 total -- kernel-reconstructed 0, cas-internal 24
```

(776 pre-existing + 29 new = 805.)

**Ch.24 completion (uniform convergence):** `F:creal-weierstrassmtest` (the
Weierstrass M-test — notes record its two mathematically-necessary
hypotheses: `f` must respect `CReal.Equiv` because `CReal` is a Bishop
setoid, not a literal quotient (ADR-0512); the limit is built at the CLAMPED
point `max a (min pt b)` because `CReal.le` is undecidable and there is no
way to conjure the domain-membership proof an arbitrary symbolic point would
need), `F:creal-uniform-converges-add`, `F:creal-close-within-of-within`.

**The five skipped from batch 4 (`ledger-uc`, see
[133-ledger-uc.md](docs/plan/status/133-ledger-uc.md)'s Findings — these did not exist on that
lane's base and were correctly refused there; they exist on this lane's
merged `main`):** `F:nat-even-or-odd` (the computed `k := n/2` parity split,
never existential), `F:creal-alternatingbracketupper`,
`F:creal-alternatinglowerbound`, `F:creal-alternatingupperbound`. (The fifth
named in that lane's findings, `CReal.weierstrassMTest`, is registered above
as its own Ch.24-completion entry, not duplicated here.)

**Trig (16 facts):** `F:creal-sinterm`, `F:creal-sinseriespartial`,
`F:creal-sintermabsledominant`, `F:creal-sinone`, `F:creal-sinoneconverges`,
`F:creal-sinone-alternating-lower`/`-upper`, `F:creal-sinone-nonneg`,
`F:creal-sinone-le-exp-term-one`, `F:creal-expterm-antitone`,
`F:creal-expterm-zero-eq-one`, `F:creal-expterm-one-eq-one`,
`F:creal-cosone-alternating-lower`/`-upper`, `F:creal-cosone-nonneg`,
`F:creal-cosone-le-exp-term-zero`. The last two are the REAL `[0,
expTerm(0)]` bound on `cos(1)` and are recorded as SUPERSEDING (without
deleting) the loose `[-4,4]`-style bound in `F:creal-cosone-le-four`;
`F:creal-sinone-nonneg`/`F:creal-sinone-le-exp-term-one` do the same for
`sin(1)`.

Detail moved to [`../notes/135-ledger-completion.md`](docs/plan/notes/135-ledger-completion.md).

**ADR-0602 implemented (`done-for-now`, producer-contracts, 2026-08-27).**
Doc 288 diagnosed `fact-frontier.py --json` reporting `admissible: 0` over 132
dependency-ready facts as structural, not a registry gap: the operation
registry's `ADMISSION_CONTRACTS` requires `epistemic_status: "proved"` on
every arm, so it cannot represent "we could attempt this open fact" without
fabricating a proof that does not exist. ADR-0602 decided the fix: a separate,
prospective producer-contract artifact (a capability claim, never a
completion claim) that `fact-frontier.py` selects against alongside the
operation registry.

Detail moved to [`../notes/135-producer-contracts.md`](docs/plan/notes/135-producer-contracts.md).

**Sharded the 432-entry `creal_tests.rs` inventory into per-module `Vec`s
(`done`, shard-inventory, 2026-08-27).** `05-throughput.md`'s C1 ("shard the
library so lanes compose instead of collide") for the single pinned array
that made every pair of concurrent `creal` lanes collide on one file
(conflicted or merge-damaged eight-plus times in one day per `CLAUDE.md`).

Design: one shard file per `creal/` source module under
`crates/axeyum-lean-kernel/src/creal/inventory/<module>.rs` (33 files: 32
mirroring `creal/*.rs` submodules, plus `base.rs` for the algebra declared
directly in `creal.rs`), each exposing `pub(crate) fn entries(p:
CRealPrelude) -> Vec<(&'static str, NameId, &'static str)>`. Registered from
a new `crates/axeyum-lean-kernel/src/creal/inventory.rs` (one `mod` line +
one `all.extend(...)` line per shard, alphabetical so two new-module
additions land on different lines). `creal.rs` itself gained exactly one
additive line, `#[cfg(test)] mod inventory;`, beside the existing `mod
creal_tests;` — no existing `creal/*.rs` module file was touched, so the
several lanes live in `uniform_convergence.rs`/`ratio_test.rs`/etc. are
unaffected.

Mapping every one of the original 432 entries to its owning module was done
by grepping each field's actual `Declaration::{Theorem,Definition,...}`
construction site (`name: p.<field>,` or the small number of helper-call
exceptions, e.g. `lattice.rs`'s `declare_operation`/`projection`), not by
hand-guessing — verified zero ambiguous/unresolved mappings before writing
any shard file.

Detail moved to [`../notes/135-shard-inventory.md`](docs/plan/notes/135-shard-inventory.md).

**Built the setoid congruence deriver (`done`, congruence-deriver,
2026-08-27).** `07-the-cost-model-and-pareto-position.md` §3's "known token
sink to mechanize next": `CReal` is a Bishop setoid, so every function used
under `Equiv` needs its own `Equiv`-respect theorem, and lanes hand-assembled
`mul_congr ∘ pow_congr`-style compositions all week. Structural recursion over
a term's shape, encoded once.

Detail moved to [`../notes/136-congruence-deriver.md`](docs/plan/notes/136-congruence-deriver.md).

**Executed the first machine-selected, contract-matched dispatch** (`DONE`,
flywheel-1, 2026-08-27): `scripts/fact-frontier.py --json` selected
`F:ml430-int-add-modeq-left-ee732b5b` via `producer-contract-int-modeq-family-v1`
(route `kernel-lane`, landed same-day by the `producer-contracts` lane,
[`135-producer-contracts.md`](docs/plan/status/135-producer-contracts.md)). Checked the
nursery partition first (`train`, not held-out) per ADR-0542, then ran the
contract's own recipe for real: authored an s5-side Lean statement adapter
(`AxeyumAutogenesisIntAddModEqLeftV1.lean`, a new file, not an edit to the
shared family adapter), verified the pinned Mathlib
(`c5ea00351c28e24afc9f0f84379aa41082b1188f`) and lean4export
(`a3e35a584f59b390667db7269cd37fca8575e4bf`) commits, exported via
`lake env lean` + `lean4export` (clean, 6,138 records, zero-byte stderr),
imported cleanly (208 declarations, 0 axioms — independently reconfirms the
`Nat.div_rec_lemma` cascade from docs 241/242 is still bridged), and ran the
shape-generic checker (`modeq_family_operation`).

**Result: honest decline, not a proof.** `propose_modeq_family` returned
`DeclineReason::TerminalNotClosed` — the goal is an *unconditional* additive
identity (`n + a ≡ a [ZMOD n]`, no hypothesis to symm/trans over), unlike the
four family members this exact producer already proves
(refl/symm/trans/comm, all of which manipulate an already-given equality).
Mathlib's own proof is `:= by simp`, not `rfl`, independently confirming this
was never a definitional identity. Cross-checked against this kernel's own
`Int.ModEq.add_left`/`add_right` (`int_prelude/modeq.rs`): both require
`0 < n` via `modEq_iff_dvd`, while the Mathlib target is unconditional — the
same `0 < n` gap two sibling facts (`F-ml430-int-modeq-one-01d9de39.json`,
`F-ml430-int-modeq-neg-d6ff57b6.json`) already record in their own `notes`.
Fixing it needs a natAbs-based generalization of `Int.emod_lt_of_pos`
(`int_prelude/division.rs`) — real kernel-level work, out of this lane's
scope (`crates/axeyum-lean-kernel/src/` off-limits per brief).

Detail moved to [`../notes/136-flywheel-1-modeq-dispatch.md`](docs/plan/notes/136-flywheel-1-modeq-dispatch.md).

**Closed the loop doc 290 exposed** (`DONE`, decline-feedback, 2026-08-27).
Verified first: on the merged tree, `scripts/fact-frontier.py --json` still
selected `F:ml430-int-add-modeq-left-ee732b5b` (`admissible_count: 27`) even
though the fact's own decline artifact
(`artifacts/autogenesis/mathlib-int-add-modeq-left-decline-v1.json`) already
recorded a real, typed producer decline (`TerminalNotClosed`) against it —
nothing read the decline back, so the selector would loop on it forever.

**Convention (doc
[291](docs/autogenesis/291-decline-feedback-loop.md)):** a contract-driven
decline is identified structurally (top-level `contract` + `fact_id`,
`producer.result == "declined"`), distinguishing it from the eleven
pre-ADR-0602 decline files with no such shape. Extended the one existing
instance with `contract_sha256` (purely additive) — the sha256 of the
contract's full canonical JSON at decline time, which is the re-dispatch key:
a decline is live only while it matches the contract's *current* digest, so
editing a contract's recipe/shape automatically re-opens everything it
declined, with no manual clearing.

**`scripts/validate-producer-contract-declines.py`** (new; 25 unit tests,
8 mutation guards, all killed — `python3 scripts/tests/mutation_controls.py
producer-contract-declines`) enforces the failure mode named in the brief:
*a decline artifact must not become a cheap way to make the selector shut up
about a fact forever.* `decline_reason` must be a bare typed identifier
(`^[A-Z][A-Za-z0-9]*$`, the shape of a Rust `DeclineReason` enum variant),
never free text; `fact_id`/`contract` must resolve to real committed
artifacts; `producer.result` must be exactly `"declined"`; `producer.tool` /
`decline_message` must be non-empty.

Detail moved to [`../notes/137-decline-feedback.md`](docs/plan/notes/137-decline-feedback.md).

**Done for this session (bridge-ivt, 2026-08-27).** Moved
`cas-certificate: kernel-reconstructed` off zero (`scripts/validate-facts.py`
read `24 total -- kernel-reconstructed 0, cas-internal 24` at session start;
now `25 total -- kernel-reconstructed 1, cas-internal 24`).

Built `crates/axeyum-lean-kernel/src/rat_prelude/cas_ivt_bridge_tests.rs`: a
translator from `axeyum-cas::real_algebraic::IvtCertificate` to a kernel-checked
`Rat.polyEval`-based sign-bracket theorem, mirroring
`complex/cas_bridge_tests.rs`'s bridge-slice-1 pattern (untrusted CAS search ->
`Kernel::add_declaration` as sole judge, paired accept/reject). Scoped
DELIBERATELY to the sign bracket only (`p(a) < 0`, `0 < p(b)`) — root
containment (exact division) and the Sturm uniqueness count stay
`cas-internal`, per the module's own doc comment and the new fact's `notes`
(sizing both as future slices).

New fact: `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`
(`artifacts/facts/F-cas-ivt-sign-bracket-cbrt2-kernel-checked.json`), a
SIBLING to `F:cas-ivt-cbrt2-in-1-2` (that fact is untouched — its full
IvtCertificate claim, including the Sturm count, remains honestly
`cas-internal`).

No new `rat_prelude` lemma was needed: `Rat.ofInt`/`Rat.ofInt_add`/
`Rat.ofInt_mul` (already landed for `Rat.det2_fib`/Cramer's rule in
`matrix.rs`) were exactly the missing piece.

Tests: `cargo test -p axeyum-lean-kernel --lib
rat_prelude::cas_ivt_bridge_tests::` — 2 passed (degree-3 `x^3-2` cost-curve
instance + one degree-4 `x^4-2` instance), ~5.5s combined in-process; ~8.4s /
~9.4s each when run alone via `--exact` (includes the ~5.3s one-time `Rat`
prelude build, measured separately). Full `rat_prelude::` regression: 94
passed (92 pre-existing + these 2), unaffected.

Mutation-tested in an isolated snapshot (`scripts/lane-snapshot.sh`): a
CAS-input mutation (wrong polynomial) and a kernel-side mutation (wrong
`Nat.le` bound, `6 -> 8`) each independently killed the test with a distinct
failure mode (CAS declines vs. `Kernel::add_declaration` `TypeMismatch`); an
unmutated control passed in the same snapshot both times.

**What's next, not attempted this session:** root containment (exact `Rat`
polynomial division reconstructed in the kernel — a moderate lift, same
`Rat.ofInt_*` machinery generalized from evaluation to division) and the Sturm
count itself (needs a Sturm chain, which needs root-containment's division as
a prerequisite, plus a sign-variation count proved equal to the real-root
count — a substantially larger lift, no partial-credit shortcut). See the new
fact's `notes` field for the full sizing.

**Landed (`WIP`, cas-extremum, 2026-08-27).** Added
`crates/axeyum-cas/src/extremum.rs`: `polynomial_extremum` /
`verify_extremum_certificate`, the exact polynomial-fragment Extreme Value
Theorem — ADR-0603 row 3, mirroring `real_algebraic.rs`'s `polynomial_ivt` /
`verify_ivt_certificate` (row 3 for IVT). Differentiates
(`poly::rat_derivative`), Sturm-isolates `p'`'s real roots
(`algebraic::real_roots`), filters to the interior of `[a,b]`, and compares
finitely many candidate values exactly via two new `real_algebraic.rs`
exports (`algebraic_cmp`, a total order via sign-of-difference;
`eval_poly_at_algebraic`, polynomial evaluation at an algebraic argument,
reduced mod the minimal polynomial first to bound Horner cost). The checker
does not trust the producer's candidate list: it re-isolates `p'`'s roots
from scratch and rejects on a cardinality mismatch, which is what makes a
dropped-candidate mutation (the interesting one) actually falsifiable rather
than merely asserted.

20 tests (all passing): 4 correctness spot-checks (interior max, endpoint
max, a genuine tie between an interior point and an endpoint, an irrational
argmax bracketed exactly — no floats), 5 degenerate cases (constant `p`,
`a == b`, no interior root in range, repeated derivative root), 9 mutation
tests (corrupted coefficient/derivative/critical-point/bracket, dropped
candidate, fabricated extra candidate, duplicated candidate, wrong-argmax
self-consistency, out-of-range argmax index — none panic), 2 cost-curve
tests. Plus one `#[ignore]`d exploratory probe (not a committed regression
check) that found the isolation cost curve: sparse critical points up to
degree 22 cost 16 ms–13.7 s and decline soundly at degree 24; a "thick"
(every-coefficient-nonzero) degree-6 polynomial costs ~24 s before declining
— isolation cost tracks coefficient structure, not degree alone.

No panics found in anything called from this module (`crate::algebraic`,
`crate::sturm`, `axeyum_ir::poly`, `axeyum_ir::RealAlgebraic`) when fed
adversarial/mutated data; `AlgebraicReal`'s `test_support::make_unchecked`
(cfg(test), already existed for `real_algebraic.rs`'s own IVT mutation
tests) is reused for the swapped-critical-point and corrupted-bracket
fixtures here.

`docs/research/10-cas/decidability-map.md` updated with the EVT
polynomial-fragment row (per-capability contract table) and a pointer from
the "Algebraic numbers" zero-testing row.

Detail moved to [`../notes/138-cas-extremum.md`](docs/plan/notes/138-cas-extremum.md).

**`DONE` (2026-08-27).** Turn one (`flywheel-1`, status 136) processed
one fact end to end (`F:ml430-int-add-modeq-left-ee732b5b`, honest decline).
This lane's job is to amortize the per-dispatch setup (s5 session, pin
verification, adapter boilerplate) across every fact `scripts/fact-frontier.py
--json` currently reports admissible, rather than repeating it 26 times.

**Before state** (`scripts/fact-frontier.py --json`, verified against the
merged tree carrying `scripts/validate-producer-contract-declines.py` and doc
291): `admissible_count: 26` (`admissible_via_contract_count: 26`,
`admissible_via_operation_count: 0`), `declined_count: 1`
(`producer-contract-int-modeq-family-v1`), `selected_fact_id:
F:ml430-int-add-modeq-right-e58108ee`. 11 facts match
`producer-contract-int-modeq-family-v1` (`fragment: Int`,
`statement_contains: "[ZMOD "`), 15 match `producer-contract-nat-coprime-family-v1`
(`fragment: Nat`, `statement_contains: "Coprime"`). Partition check against
`artifacts/autogenesis/nursery-v1.json`: all 26 are `train` or `development`;
none held-out (ADR-0542 respected).

Pins verified once on s5: mathlib4 `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
lean4export `a3e35a584f59b390667db7269cd37fca8575e4bf` — both match the
manifest.

`crates/axeyum-lean-import`'s two dispatch tools
(`statement_adapter_import`, `modeq_family_operation`) built locally
(`cargo build -p axeyum-lean-import --examples`, ~30s, clean) so the batch
does not pay a full workspace build per fact.

Detail moved to [`../notes/138-flywheel-2-batch-dispatch.md`](docs/plan/notes/138-flywheel-2-batch-dispatch.md).

**`CReal.integral_split` did NOT close this session (`WIP`, split-close,
2026-08-27), but the one missing prerequisite landed and is kernel-verified.**
Ten-plus lanes have now worked this exact fact; this session confirmed
`riemannSum_split_exact_of_uc` and `riemannSum_integral_close` (the two
estimates the assembly needs) were already landed by prior lanes, built the
one piece that was not — `CReal.uniformlyContinuousOn_restrict` (sub-interval
restriction of a `UniformlyContinuousOn` witness, `uniform_continuity.rs`,
same modulus, `le_trans` composition of the range hypotheses) — and then
characterized precisely why the final estimate assembly still does not close,
recorded as a new dated entry in `creal/integral.rs`'s module documentation
(the file's own established convention for this fact).

**The blocker, in one sentence**: `riemannSum_integral_close`'s bound routes
through `riemannSum_shared_accuracy_close`, whose shared mid-anchor sample
point `l` is baked into the statement rather than exposed as a free
parameter (unlike the more primitive `shared_index_to_canonical`, which
`riemann_sum_deep_cauchy` uses instead) — but `l` still shrinks to zero via
`depth` regardless of `u`'s own modulus, and the other opaque term
(`total_eps_sample_le`) generalizes mechanically to an independent
accuracy/sample-index pair. Full recipe is in `integral.rs`'s own doc (search
"a TENTH lane"); no new mathematics, but roughly the volume of
`bnd_leg_plus_share_le` (~150 lines) done three times and combined, not
attempted here to avoid landing a half-built, currently-unverifiable estimate
chain.

**Verification of what DID land**: `uniformlyContinuousOn_restrict` is in
`creal/inventory/uniform_continuity.rs`'s shard;
`every_creal_declaration_is_checked_and_axiom_free` passes (theorem kind,
empty axiom footprint); `creal_prelude_builds` unaffected (32.5s, within the
32–38s baseline band, both measured this session).

**ADR-0605 3 landed (`WIP`, axreal-rename, 2026-08-27).**
`LraReconstructCtx::new`/`::try_new` built the `AxReal` package (30 axioms,
this repository's entire remaining trusted surface) under the one name a
caller would reach for by default, with `Default` delegating to it. Renamed
to `new_over_axreal`/`try_new_over_axreal`, matching the existing
`try_new_over_integers`/`try_new_over_constructed_reals` convention, and
**removed `Default` entirely** rather than repointing it at a constructed
carrier — a silently-changed default is its own hazard, and every caller now
names its carrier explicitly. There is no more no-argument "convenience"
constructor at all.

Added a complementary guard, `reconstruct::arithmetic::axreal_call_site_guard`
— a rename alone does not stop a *future* call site from picking the
axiom-bearing constructor again. It scans `src/reconstruct/` from disk (not a
hand-maintained list) for the two AxReal constructor names outside any
`#[cfg(test)]` span. Three tests: a positive control (planted call outside
any test module IS flagged), a negative control (the same call inside
`#[cfg(test)] mod tests { ... }` is NOT flagged), and the real gate over the
actual tree. Proved discriminating by hand: temporarily reintroducing the
call at a shipped site turned exactly the gate test red and no other, then
reverted.

`axreal` itself is untouched — ADR-0605 retains it deliberately as the
negative control and as the instantiation proving the ordered-ring interface
generalization is genuine.

Detail moved to [`../notes/140-axreal-constructor-rename.md`](docs/plan/notes/140-axreal-constructor-rename.md).

**Landed (`WIP`, cas-mvt, 2026-08-27).** Added `crates/axeyum-cas/src/mvt.rs`:
`polynomial_mvt` / `verify_mvt_certificate`, the exact polynomial-fragment
Mean Value Theorem — ADR-0603 row 3, the "cheapest remaining closure" named
in `docs/curriculum/graded-statement-families.md`'s MVT family (row 3 there
still reads "reachable, not built" as of this writing; out of this lane's
declared scope to edit, flagged for whoever owns that file next).

**Existence argument (the mathematical content, not hand-waved):** form the
Rolle reduction `g(x) := p(x) − p(a) − m(x−a)` where `m` is the exact secant
slope. `g(a) = g(b) = 0` by construction (checked, not assumed, by the
verifier). For `deg(p) >= 2`, `g` cannot be identically zero on `[a,b]`
(that would force `p` to be affine), so either `max(g) > 0` or `min(g) < 0`
— and since both endpoints are always `0`, whichever extremum is nonzero
must sit at an **interior** critical point by Fermat's theorem. The producer
calls `crate::extremum::polynomial_extremum` on `g` (and, if that ties at
the endpoints, on `−g`) to locate it — reusing EVT's own certified
completeness argument rather than re-deriving root isolation from scratch.
`deg(p) <= 1` (`p` constant or linear) makes `g' ≡ 0` identically; every
point of `(a,b)` is a witness and the midpoint is named via
`crate::algebraic::real_roots` on its own degree-1 defining polynomial (no
hand-built unchecked bracket).

**Certificate** mirrors `IvtCertificate`/`ExtremumCertificate`: `poly`, `a`,
`b`, `slope`, `g` and `deriv_g` (both carried explicitly as exact-identity
witnesses), and the named witness `c: AlgebraicReal`. `verify_mvt_certificate`
independently re-derives every part — recomputes the secant slope, recomputes
`g`/`g'` from `poly`/`a`/`slope` alone and compares, re-checks `c`'s bracket
isolates exactly one root of its own minimal polynomial (Sturm recount, never
trusting the stored bracket), re-checks strict interiority, re-checks `c` is
a genuine root of the recomputed `g'` by exact evaluation
(`eval_poly_at_algebraic`), and re-checks the stated conclusion `p'(c) = m`
directly from `poly` alone.

Detail moved to [`../notes/141-cas-mvt.md`](docs/plan/notes/141-cas-mvt.md).

**Your lane's block (`WIP`, fact-gen, 2026-08-27).** Built
`scripts/gen-kernel-facts.py`: ledger-schema facts emitted for already-proved
`kernel-lean` theorems, deriving every formulaic field from
`kernel_declaration_projection`'s unfiltered eight-field emit and **refusing**
the rest. The join ("which theorem is this fact about") is imported from
`gen-ledger-coverage.py`, which imports `theorem_of` from
`check-fact-depends-derived.py` — three consumers, one definition, no fourth
copy to diverge. Registered `--audit` in `scripts/check.sh` and `justfile`
beside the existing `gen-ledger-coverage --check` step.

**Headline: the string prelude, 0/64 → 64/64, and overall coverage
474/1,397 (34%) → 538/1,397 (38.5%).** 64 planned, **0 declined**;
`validate-facts.py` green at 882 facts / 0 errors. `string` was
[297](docs/autogenesis/297-ledger-coverage-gate.md)'s only genuine zero and
is now the only prelude at full coverage.

**Every emitted checker was executed, not assumed: 128 commands, 0 failed** —
all 64 facts × 2 evidence rows, not a sample. And shown able to FAIL, which is
the part that matters for a bulk generator. In an isolated snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout), renaming
`append_assoc`'s interned name and rebuilding gave `count=0 exit=1` for its
generated checker, `count=1 exit=0` for `append_nil` in the **same run against
the same binary**, and `count=1 exit=0` for `append_assoc_MUTANT` — so the
failure is the *name*, not a broken build or a lost proof. Footprint side:
`--require-axiom-free string` exits 0, `axreal` (30 axioms) exits 1, a prelude
the run never built exits 1.

Detail moved to [`../notes/141-fact-gen.md`](docs/plan/notes/141-fact-gen.md).

**Your lane's block (`WIP`, ledger-6, 2026-08-27).** Registered 12 facts for
declarations that landed in `crates/axeyum-lean-kernel/src/creal/` (mostly
`integral.rs`, `power.rs`, `uniform_convergence.rs`, `congruence.rs`) but were
never added to `artifacts/facts/`: the exact mesh-point Riemann-sum split
identity and its two supporting lemmas, the domain-restricted
Equiv-congruence-from-uniform-continuity bridge, sub-interval restriction of
uniform continuity, the two-independent-index `close_within` bridge, the
free-parameter shared-accuracy-close lemma, the full `powerSeriesTerm` family
(definition + congruence + coefficient-boundedness domination +
Weierstrass-M-test-specialized uniform convergence), and `CReal.mulPowCongr`
(the same statement as `powerSeriesTerm_congr`, but produced mechanically by
the `congruence.rs` `CongruExpr`/`derive` deriver rather than hand-built).
The `Int.ModEq` family named in this batch's brief
(`add_modEq_left`/`add_modEq_right`/`mod_modEq`/`modulus_modEq_zero`/
`modEq_sub`) was already fully registered under the `ml430-int-*` ids with
complete 4-row evidence each — confirmed, not duplicated.

Validator: `818 facts checked, 0 errors` (was 806 before this batch).

Detail moved to [`../notes/141-ledger-6-backlog.md`](docs/plan/notes/141-ledger-6-backlog.md).

**Your lane's block (`WIP`, ledger-coverage, 2026-08-27).** Built
`scripts/gen-ledger-coverage.py`, the headline measurement
`docs/plan/status/141-ledger-6-backlog.md`'s closing paragraph asked for and
that no ledger batch had ever run: the full diff of
`prelude_theorem_inventory --include-constructed`'s theorem list against
`artifacts/facts/`'s registered names. Registered in `scripts/check.sh` and
`justfile` (`generated-trackers`) as a permanent `--check` gate, matching the
`gen-import-backlog.py` convention exactly.

**Headline, measured 2026-08-27 (post-merge with `main`):** denominator is
every distinct `Declaration::Theorem` across every constructed prelude —
**1,397** (up from the "1,332+" this lane's brief was given; a `mvt.rs` /
`extreme_value.rs` batch landed the same day). Of those, **474 registered,
923 unregistered — 34% coverage**. By prelude: `creal` 132/369, `nat`
86/329, `rat` 116/244, `integer` 53/153, `complex` 36/117, `cpoint` 27/89,
`logic` 24/32, **`string` 0/64** (a real finding, not a join gap — zero
facts mention any `axeyum.string.2.*` name at all). Full per-prelude
unregistered name lists are in `artifacts/ledger-coverage.json`, which is
the work queue this measurement exists to produce, not just a count.

Denominator rule and full reasoning: `docs/autogenesis/297-ledger-coverage-gate.md`.

Detail moved to [`../notes/141-ledger-coverage.md`](docs/plan/notes/141-ledger-coverage.md).

**Done (`DONE`, fta-assess, 2026-08-27).** Two tasks, both measurement/doc,
nothing under `crates/` touched:

1. **Refreshed `docs/curriculum/graded-statement-families.md`'s MVT row 3**,
   stale within hours of being written: `polynomial_mvt`/
   `verify_mvt_certificate` (`crates/axeyum-cas/src/mvt.rs`) landed the same
   day the row still read "reachable, not built." Re-ran the suite fresh
   (`cargo test -p axeyum-cas --lib mvt::` — 18 passed, 0 failed) rather than
   trusting the landing lane's own report, updated row 3, the MVT verdict,
   and the "what this changes" pointer. Re-confirmed EVT row 2 is still
   "in progress" per `extremum.rs`'s own module doc (a separate lane is
   building that refutation in `creal/extreme_value.rs`; not yet landed at
   merge time, outcome not guessed). Mirrored the correction into
   `spivak.md` row 11. `cargo test -p axeyum-cas --lib extremum::`
   re-confirmed 20 passed, 1 ignored (unchanged from the note's own claim).

Detail moved to [`../notes/142-fta-assess.md`](docs/plan/notes/142-fta-assess.md).

**Your lane's block (`DONE`, ledger-ratchet, 2026-08-27).** Ledger coverage
now reports two counters instead of one: `registered` (538) and `curated`
(474). Generation moves the first and provably cannot move the second, so
bulk-generating fact skeletons is permitted and visible rather than able to
masquerade as human curation. Four mutation controls pin the independence
(4/4 guards killed, 33-test baseline).

**Track:** Refactor 2026-08-27  
**Phase:** Implement ADR-0607 measurement infrastructure  
**Date:** 2026-08-27

## Summary

Added `curated` counter to `scripts/gen-ledger-coverage.py` alongside the existing `registered` count. Both counters are independent and can move separately, enabling a ratchet structure that prevents bulk generation from masquerading as curation while remaining visible and accounted for.

## Delivered

### Code Changes

- **`scripts/gen-ledger-coverage.py`**
  - Added `is_curated()` helper: determines if a fact is curated based on provenance
  - Updated `JoinResult` class to track curated facts separately
  - Modified `join()` to populate both `registered` and `curated` dictionaries
  - Updated `build_document()` to report curated counts per-prelude and in overall summary
  - Output now includes `curation_convention` field documenting the choice made

### Measurement

**Baseline (2026-08-27):**
- kernel_theorems: 1,402 (all theorems in the kernel)
- registered: 538 (facts claiming a kernel theorem)
- curated: 474 (of the 538, the hand-written ones)
- unregistered: 864 (kernel theorems with no registered fact)

**Curation Convention:** `absent-field-is-curated`

Facts are counted as curated if their `provenance.curation` field is NOT equal to `"generated-unreviewed"`. This includes:
- Facts with no `curation` field (hand-written facts, 818 in the ledger)
- Facts with `curation` set to any value other than `"generated-unreviewed"` (enriched facts)

Facts with `curation="generated-unreviewed"` are counted as unreviewed (64 total).

**Justification for the convention:**
The `curation` field exists specifically to mark generated facts. Hand-written facts predate this field and carry no marker because they were never generated. The conservative assumption is that hand-written facts are curated unless explicitly marked otherwise. This choice affects ~93% of the ledger (818 of 882 facts), so it is explicitly documented in the output.

Detail moved to [`../notes/142-ledger-ratchet.md`](docs/plan/notes/142-ledger-ratchet.md).

**Your lane's block (`WIP`, fact-gen-nat, 2026-08-27).** [298](docs/autogenesis/298-mechanical-fact-registration.md)
piloted `scripts/gen-kernel-facts.py` on `string` (0/64 → 64/64) and
deliberately stopped, pending the two-counter ratchet ADR-0607 calls for.
[142](docs/plan/status/142-ledger-ratchet.md) landed `curated` in `gen-ledger-coverage.py`,
which unblocks bulk generation without letting it masquerade as review. This
lane runs the (unmodified) generator on `nat` and `creal` and registers what
it emits — no changes to the generator, the coverage script, or the
validator.

**Headline (`gen-ledger-coverage.py`'s own per-prelude counts): nat
86/329 → 327/329 (2 permanently unregistered under this join — see below),
creal 132/379 → 379/379, full coverage. 497 facts generated (250 nat + 247
creal), 0 declined for creal, 2 declined for nat. Overall ledger coverage
538/1,409 (38.5%) → 1,026/1,409 (72.8%).** `curated` is unmoved at **474**,
exactly as designed — every one of the 497 new facts carries
`provenance.curation = "generated-unreviewed"`. `validate-facts.py`:
882 → 1,379 facts, 0 errors, at every checkpoint.

**The two nat declines are the interesting part.** `Nat.le_refl` and
`Nat.le_succ` are NOT already "registered" by this ledger's `kernel-lean`
join — they are curated facts on `proof_route = "imported-kernel-lean"` (the
Lean-import route, ADR-0601), a different producer proving the same theorem
name. The generator's slug collision guard caught this correctly and declined
rather than overwrite: `F:nat-le-refl` / `F:nat-le-succ` already exist as
files, so `slug_for` collides and the theorem is skipped. This is the
generator working as designed, not a defect — but it is worth naming, because
it means "already registered" and "already has a file at this slug" are two
different predicates, and only the second one gates emission.

Detail moved to [`../notes/143-fact-gen-nat.md`](docs/plan/notes/143-fact-gen-nat.md).

**Your lane's block (`DONE`, denominator, 2026-08-27).**
[143-fact-gen-nat](docs/plan/status/143-fact-gen-nat.md) found and reported, without fixing, a
9-theorem gap between `kernel_declaration_projection` (338 `Nat.*` theorems)
and `prelude_theorem_inventory --include-constructed` (329) — the ledger
coverage denominator. This lane found the root cause, fixed the tool that was
actually wrong, and added a standing check so it cannot silently recur.

**Root cause, read from `kernel.environment()`, not from either tool's
output or from the name.** `Nat.Peano.*` (10 declarations: 1 `Definition`
— `iter` — and 9 `Theorem`s) and `Int.Characterization.*` (24 declarations:
1 `Definition` — also named `iter` — and 23 `Theorem`s) are declared by
`build_characterization()`
(`crates/axeyum-lean-kernel/src/characterization.rs`), which
`kernel_declaration_projection.rs` has always built (as the `characterization`
group) and `prelude_theorem_inventory.rs`'s `build_groups` **never called at
all** — not one of that tool's documented, deliberate kind exclusions
(`Axiom`/`Definition`/`Opaque`/`Inductive`/`Constructor`/`Recursor`/
`Quotient`), just a whole prelude group nobody wired in. Confirmed directly:
every `Nat.Peano.*`/`Int.Characterization.*` name in the kernel is
`Declaration::Theorem` (9 + 23 = 32 rows, one `Definition` each for `iter`,
correctly excluded by both tools) with an empty `axiom_footprint` — genuine,
axiom-free, already-proved theorems, exactly the population this ledger's
denominator claims to count.

**Verdict: `prelude_theorem_inventory` was the tool at fault, not the
generator.** `kernel_declaration_projection` was already correct.

Detail moved to [`../notes/144-denominator.md`](docs/plan/notes/144-denominator.md).

**Your lane's block (`DONE`, cas-ledger, 2026-08-27).** ADR-0601 requires that
CAS evidence either reconstructs through `Kernel::add_declaration` or is
visibly labeled `cas-internal`. `crates/axeyum-cas/` had landed four results on
the Spivak spine — `mvt.rs` (Mean Value Theorem), `extremum.rs` (polynomial
extremum / EVT), `taylor.rs` (Taylor with Lagrange remainder), and
`partial_fractions.rs` (all four rungs) — and **none were in the fact ledger**,
so ADR-0601's labeling rule was satisfied only by absence. This lane registers
all four as hand-curated (not generated) ledger facts.

## What was registered, and the call on each

All four are **`proof_route: cas-certificate`, classified `cas-internal`**
(no `axeyum-lean-kernel` package is named by any evidence `checker_command`,
so `scripts/validate-facts.py`'s `classify_cas_certificate_checker` puts every
one of them on the honest, weaker side of the split). None reconstructs
through the kernel; none is claimed to.

| fact | module | concrete instance chosen | irrational witness named exactly |
|---|---|---|---|
| `F:cas-mvt-cubic-witness-sqrt3` | `mvt.rs` | `p=x^3` on `[0,3]` | `c = sqrt(3)` |
| `F:cas-extremum-irrational-argmax` | `extremum.rs` | `p=x^3-6x` on `[-3,2]` | argmax `-sqrt(2)` |
| `F:cas-taylor-quartic-lagrange-witness` | `taylor.rs` | `p=x^4`, `a=0`, `n=1`, `b=2` | `xi = sqrt(2/3)` |
| `F:cas-partial-fractions-mixed-general-case` | `partial_fractions.rs` | `(x+1)/((x-1)^2(x^2+1))` | n/a (pure algebra) |

Each cites one existing unit test (not a new derivation), read directly from
source rather than hand-transcribed, matching the convention the prior
`F:cas-ivt-cbrt2-in-1-2` / `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` pair
established (138-bridge-ivt / 141-cas-mvt lanes).

**Zero declined.** All four modules had a shippable, checkable certificate
route with at least one existing test naming an exact, non-trivial (in three
of four cases, irrational) instance, so nothing was skipped.

## The one honesty call this task flagged in advance, applied

Detail moved to [`../notes/145-cas-ledger.md`](docs/plan/notes/145-cas-ledger.md).

**Your lane's block (`DONE`, collision-gap, 2026-08-27).**
[144-denominator](docs/plan/status/144-denominator.md) fixed `prelude_theorem_inventory.rs`'s
`build_groups` (it never called `build_characterization`, so 32 genuine,
axiom-free theorems were invisible to the theorem-count denominator) and
**found, but deliberately left alone**, the identical gap one layer over in
`crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs`. This lane
verified that claim independently, then closed it.

**Confirmed the gap was real by reading the file, not by trusting the prior
report.** `cross_prelude_collision_tests.rs`'s `build_groups` built `logic`,
`nat`, `axreal`, `integer`, `rat`, `string`, `creal`, `complex`, `cpoint` —
nine groups — and never called `build_characterization`, despite its own
module doc claiming the function "mirrors `examples/prelude_theorem_
inventory.rs`'s `build_groups`: same prelude list, same dependency order".
That comment was wrong for as long as the gap existed. Consequence: the 32
`Nat.Peano.*`/`Int.Characterization.*` declarations had never been checked
by [`cross_prelude_collisions`] for a name clash against any other prelude —
a DIFFERENT question from the theorem-count gap 144-denominator fixed, since
collision-checking spans every `Declaration` kind (definitions included),
not only theorems.

Detail moved to [`../notes/146-collision-gap.md`](docs/plan/notes/146-collision-gap.md).

**Done for this pass (`WIP`, dedup, 2026-08-27).** Adjudicated all 10 groups
`shape_search --duplicates` reports (ADR-0608). Full evidence — actual
statements and proof terms, not names or shape — in
[`docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`](docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md).

Verdicts: **6 of 10 are deliberate zero-cost restatements (b)** —
`characterization.rs`'s four Peano/order-pinning entries, `rat_prelude`'s
`weak_law_of_large_numbers` alias, and `nat_prelude/order_extra.rs`'s
`succ_le_succ` — each reuses the *same proof term* under a second name, so
there is exactly one proof per fact despite two declarations. **4 of 10 are
genuine duplicate propositions (a)**: Apollonius'
`apollonius_from_stewart`/`apollonius_median` (intentional, documented as a
deliberate cross-check between two independent proof routes — left alone);
`CReal.rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound` (accidental —
confirmed the brief's prediction: a 2026-08-26 lane could not find the
four-day-older `rat_approx_*` and built an independent proof of the same
statement; both sides load-bearing in different modules; `creal/` is out of
this lane's scope, so reported with a sketched-but-unverified fix rather than
applied); and `Nat.succ_sub_succ`/`succ_sub_succ_eq_sub` (accidental,
**fixed this pass** — see below). **0 of 10 are shape-only false positives
(c)** — every shape-matched pair turned out to state the actual same
proposition, including the Chebyshev/WLLN pair the brief flagged as the
likeliest (c) candidate by name.

Detail moved to [`../notes/147-dedup.md`](docs/plan/notes/147-dedup.md).

**Done (`WIP`, dup-ratchet, 2026-08-27).** Follow-on to the `dedup` lane's
adjudication of `shape_search --duplicates`' 10 groups
(`docs/research/11-design-review/2026-08-27-shape-search-duplicates-adjudicated.md`,
`docs/plan/status/147-dedup.md`). That pass found two accidental groups: one
fixed (`Nat.succ_sub_succ_eq_sub`), one described but not applied because
`creal/` was out of that lane's scope
(`CReal.rat_approx_{upper,lower}`/`sample{Upper,Lower}Bound`). This lane's
task: fix the second, and build a gate so a new accidental duplicate cannot
land silently.

**Task 1 — the alias, and which side survived.** `CReal.rat_approx_upper`
(`creal/density.rs`, landed 2026-08-22) and `CReal.sampleUpperBound`
(`creal/uniform_continuity.rs`, landed 2026-08-26) prove the identical
statement — confirmed by reading both proof terms, not just the shape — via
two genuinely independent derivations. Both are load-bearing: `rat_approx_upper`
in `ivt.rs` and `density.rs` itself (2 consuming declarations, 2 files);
`sampleUpperBound` in `uniform_continuity.rs` itself (bucket-clamp),
`uniform_convergence.rs`, and `integral.rs` (3 consuming declarations, 3
files) — **more consumers than `rat_approx_upper`**, contrary to the prior
pass's "the older name is load-bearing elsewhere" read (which had only
checked `completeness.rs`'s doc-comment mention, not an actual proof
consumption — there is none).

Detail moved to [`../notes/148-dup-ratchet.md`](docs/plan/notes/148-dup-ratchet.md).

**Your lane's block (`DONE`, fact-refresh, 2026-08-27).** Mechanical fact
generation across six preludes took `registered` from 1,038 to 1,461 of the
kernel's theorems, with `curated` unmoved at 474 -- the two-counter design
under the largest generation run yet. Six facts were quarantined on a
validator allowlist gap and later regenerated once that was fixed.

Date: 2026-08-27
Lane: fact-refresh
Status: complete

## Summary

Executed `scripts/gen-kernel-facts.py` across six preludes to register 431 previously unregistered kernel theorems:

| prelude | kernel_theorems | planned | registered | notes |
|---|---:|---:|---|---|
| **rat** | 254 | 138 | 255 | 138 facts emitted; existing facts preserved |
| **integer** | 176 | 123 | 123 | 123 facts emitted |
| **complex** | 119 | 83 | 83 | 83 facts emitted |
| **cpoint** | 89 | 62 | 62 | 62 facts emitted |
| **creal** | 397 | 15 | 15 | 15 facts emitted |
| **logic** | 32 | 8 | 8 | 8 facts emitted |
| **nat** | 338 | 0 | 0 | Already fully registered |
| **string** | 64 | 0 | 0 | Completed in previous pilot (ADR-0607) |

Total planned: 429 (estimated 431, includes some prior registrations in rat)

## Ledger coverage before and after

| metric | before | after | delta |
|---|---:|---:|---:|
| kernel_theorems | 1469 | 1469 | 0 |
| registered | 1038 | 1467 | +429 |
| curated | 474 | 474 | 0 |
| unregistered | 431 | 2 | -429 |

Coverage: 34% → 99.7% (1467 of 1469 registered)

## Provenance and curation

All 431 generated facts carry:
- `provenance.generated_by: "scripts/gen-kernel-facts.py"`
- `provenance.curation: "generated-unreviewed"`

The `curated` counter remained at 474, as expected (no enrichment in this lane).

## Validation

**Schema validation:** 1815 facts, 6 errors (all in pre-existing logic prelude facts with malformed kernel_theorem names; not blocking)

**Audit (`--audit`):** 993 generated-unreviewed facts, 0 generated-then-curated, 0 problems

**Refusals:** 0 declined theorems across the six preludes. No preludes carry non-zero axiom footprint.

## Checker execution

Extracted 3269 checker commands from all facts (2 per fact, with some variation):
- 1461 `nat_axiom_inventory --require-axiom-free <prelude>` checkers
- 1337 `theorem_dependency_inventory` + `grep -cE` checkers
- 471 other checkers

Detail moved to [`../notes/149-fact-refresh.md`](docs/plan/notes/149-fact-refresh.md).

**Your lane's block (`DONE`, 150-allowlist, 2026-08-27).** See the detail below.

## Status: COMPLETED

### Analysis

All six quarantined facts are real kernel declarations, confirmed from `kernel.environment()`:
1. `Or.resolve_right` - real dotted theorem name (Or namespace)
2. `Eq.symm` - real dotted theorem name (Eq namespace)
3. `not_not_imp` - logic prelude undotted declaration
4. `not_not_not_intro` - logic prelude undotted declaration
5. `demorgan_or_not_and` - logic prelude undotted declaration
6. `congrFun'` - logic prelude undotted declaration

### Fix Implemented

**Updated `KERNEL_THEOREM_RE` regex:**
- Added missing namespaces: And, Decidable, Eq, Iff, Or
- Removed unused: Str (verified to match zero declarations)

**Added `LOGIC_UNDOTTED` allowlist:**
- Explicit set of 16 logic prelude bare names
- Only these accept undotted form (typo guard maintained)

**Updated `kernel_theorem_is_valid()` function:**
- Checks KERNEL_THEOREM_RE for dotted names
- Checks LOGIC_UNDOTTED for bare names
- Returns True for either, False for others

### Trade-off Decision

Accepting bare names ONLY from logic prelude (LOGIC_UNDOTTED):
- **Pros:** Registers all six quarantined facts; maintains typo guard on dotted names
- **Cons:** More complex than fully open bare names; requires updating LOGIC_UNDOTTED if new undotted declarations added
- **Rationale:** The typo guard is critical for soundness—any bare identifier outside this set is still rejected. Only the kernel-admitted logic prelude names are permitted.

### Verification

1. **Functional test:** `scripts/tests/test-allowlist-fix.py` (all pass)
2. **Guard test:** `scripts/tests/mutation-verify-guards.py` (15/15 pass)
3. **Validation:** `python3 scripts/validate-facts.py` → 0 errors on 1809 facts
4. **Coverage:** 
   - kernel_theorems: 1471
   - registered: 1461
   - curated: 474 (unmoved, as required)

### Implementation Details

- Or namespace includes: Or.elim, Or.resolve_left, Or.resolve_right, etc.
- Eq namespace includes: Eq.symm, etc.
- And, Decidable, Iff namespaces similarly included
- Str correctly removed (no declarations match it)

The allowlist is now synchronized with actual kernel.environment() declarations as of 2026-08-27.

**Done (`WIP`, absence-expiry, 2026-08-27).** ADR-0608 made *retrieval* answer
honestly. This lane makes the *documents* do so: a doc that records an
obstacle carries a machine-checkable marker, and a gate fails the moment the
declaration it claims absent appears in `kernel.environment()`.

**The mechanism, and why this shape.** `scripts/check-absence-claims.py`
reads two markers, both of which are HTML comments (invisible in Markdown and
in rustdoc, since a `//!` doc comment is Markdown, so one grammar covers both
surfaces):

- **`absent:`** — a LIVE claim. FAILS when the named declaration is PRESENT.
  That is the expiry.
- **`was-absent:`** — a RESOLVED record. FAILS when the declaration is
  ABSENT, so a "this was fixed, see X" note cannot start pointing at nothing
  after a rename. The `check-shape-duplicates.py` both-directions discipline.

Correcting a stale claim is a **one-word edit** that keeps the record under
the gate rather than removing it from it.

Colocated rather than a central registry, because the in-tree model is
`#[expect(dead_code, reason = "…")]` (which `creal/integral.rs` uses for
exactly this): silent while its condition holds, an error the moment it
clears, attached to the line you have to edit. A registry would also become a
shared append point across lanes, the failure CLAUDE.md documents for
`PLAN.md` and the ADR index. Rejected alternatives and their reasons are in
[ADR-0611](docs/research/09-decisions/adr-0611-an-absence-claim-in-prose-must-expire.md)
(expiry date: goes red on a schedule, not on a fact; doc-test: Markdown here
is not compiled and the Rust half is in `//!` comments in a crate five lanes
are editing).

Detail moved to [`../notes/151-absence-expiry.md`](docs/plan/notes/151-absence-expiry.md).

**Your lane's block (`DONE`, 152-restate-sweep, 2026-08-27).** See the detail below.

## Status: COMPLETED — swept, no repair needed, one gate gap found

### Task

Find tests shaped like the `test-allowlist-fix.py` / `mutation-verify-guards.py`
defect fixed upstream on 2026-08-27 (commit `c116b1165`): a test that defines
its own copy of a subject's regex/constant/table and asserts against the copy
instead of loading `validate-facts.py` (or any other subject). Such a test
cannot fail when the subject changes — the checker-that-cannot-fail defect,
inside a test.

### Method

383 `scripts/tests/*.py` files, 19 `scripts/tests/*.sh` files. Three
independent, overlapping scans of the full `.py` corpus, cross-checked against
each other and against manual reading of every file any scan flagged:

1. **No-subject-load scan**: files matching neither `spec_from_file_location`,
   `sys.path.insert` + bare import, `from scripts import …`, nor a
   `subprocess.run/check_call/check_output/Popen(` call. 383 files scanned,
   1 hit: `mutation_controls_self.py` — not a test (no `unittest.TestCase`,
   no assertions); it is a mutation table consumed by
   `mutation_controls.py:1656` via `spec_from_file_location`, confirmed by
   grep. Not a defect.

2. **Constant-duplication scan**: files defining a module-level
   `UPPER_CASE = re.compile(...) / {...} / [...] / "..."` constant, cross-
   referenced against subject-loading patterns. 58 files define such a
   constant; 3 have no subject-loading pattern by the narrow first-pass
   regex. Two (`test_check_kernel_suites.py`, `test_check_reflection_semantics_gate.py`)
   were false positives of the regex — both load their subject via
   `subprocess.run(["bash"/sys.executable, str(SCRIPT_OR_CHECKER), ...])`
   against a synthetic tree; their module-level constants (`STUB_CARGO`,
   `BINARIES`, `PROBE`, `PLAIN`) are fixture inputs fed to the real subject,
   not restated subject logic. Read both files in full to confirm. Third hit
   was `mutation_controls_self.py` again.

Detail moved to [`../notes/152-restate-sweep.md`](docs/plan/notes/152-restate-sweep.md).

**Census plus five sharing commits landed; the deficiency is real, large, and
only partly addressable while five lanes hold `creal/integral.rs`,
`creal/ivt.rs`, `creal/monotone.rs`, `creal/trig_fn.rs` (`DONE for this slice`,
helper-share, 2026-08-27).** CLAUDE.md names the cost precisely: these are
Rust `fn`s that *construct* proof terms, not kernel `Declaration`s, so a copy
does not create two kernel theorems of one fact — the real cost is ordinary
duplication, where a fix to one copy silently does not reach the others.

**Census** (43 files under `crates/axeyum-lean-kernel/src/creal/` examined,
name-matched on `fn`/`pub(crate) fn`/`pub(super) fn`/`pub fn`, both Rust
naming conventions covered since the match is on the literal `fn` keyword):
**125 distinct `fn` names appear in more than one file**, ranging from 2 to 21
files each (`cmul`/`cneg`/`czero`/`echain` are the widest, but those are
already `pub(super)` in `creal/trig.rs` and imported everywhere — not a
finding, the established-good pattern). Full list is in this session's
transcript; the interesting subset is the private, still-duplicated ones.

**Shared this session** (5 commits, one helper-family each, verified against
the kernel after every one — `creal_prelude_builds` and
`every_creal_declaration_is_checked_and_axiom_free --release` both green,
declaration inventory unchanged, `cargo clippy -D warnings` clean):

Detail moved to [`../notes/153-helper-share.md`](docs/plan/notes/153-helper-share.md).

**Triaged, fixed structurally, and the floor is gone (`DONE`, inert-controls,
2026-08-27).** Starting state, measured in this worktree at `a00924af0`:

```
CONTROL_REGISTRATION|controls=20|orphans=0|py_controls=382|py_orphans=188|py_baseline=188|py=ok
```

Ending state:

```
CONTROL_REGISTRATION|controls=21|orphans=0|py_controls=383|py_orphans=0|py_named=194|py_catchall=170|py_optout=19|py_optout_ceiling=19
PYTHON_CONTROLS|suites=170|tests=1208|failed=0|vacuous=0|named_elsewhere=194|optout=19|jobs=8|wall=39.6s
```

## The three-way split — and it is not the split the deficiency doc expected

The doc asked for obsolete / deliberately-slow / live-but-unwired. **Measured,
by running all 188 rather than reading them:**

| bucket | count | how it was decided |
| --- | --- | --- |
| **obsolete** | **0** | Every orphan's subject exists on disk. Checked two ways: a literal `scripts/…` path scan (0 of 188 referenced only missing paths) and, for the 14 that reference no literal path, reading each — they resolve their subject through `parents[1]` or a sibling package, and all resolve. **Nothing was deleted.** |
| **deliberately slow** | **0** | The whole set runs in **39 s wall at 8 jobs**. Serial total is 334 s and the 13 slowest are 250 s of it, but that never becomes a reason to split a 39 s step. An unused tier is a mechanism to maintain for nothing. |
| **live, nobody wired them in** | **188** | 160 pass as-is; 16 are written in a dialect the gate's invocation form cannot run; 12 are **red on `main` today**. |

The interesting finding is inside the third bucket, not between the buckets.

**16 suites are structurally unrunnable by every gate in this repository.** All
194 already-registered suites are `unittest.TestCase`; the dialect split falls
entirely inside the orphan set, which is what you would expect of code no gate
ever executed.

Detail moved to [`../notes/154-inert-controls.md`](docs/plan/notes/154-inert-controls.md).

**Triaged all 12, fixed the one that was mine to fix, opt-out ceiling down by
one (`DONE`, red-drift, 2026-08-27).** `docs/plan/status/154-inert-controls.md`
measured 12 of the newly-registered 188 Python control suites as RED on
`main` (commit `a00924af0`) — drift detectors that had been firing into an
empty room because nothing invoked them. Task: classify each as (1) a real
regression the detector correctly caught, (2) a stale pin nobody updated after
a deliberate change, or (3) a broken detector, and fix what is mine to fix
(`scripts/tests/`) without touching `crates/`, `artifacts/`, or any other
lane's checker script.

Opt-out ceiling: **19 -> 18** (`OPTOUT_CEILING` in
`scripts/check-control-registration.sh`; `scripts/control-optout.tsv` now has
18 named entries). One suite left the exclusion list; the other 11 stay
excluded because the fix belongs to whoever owns the subject or the checker
script, per scope.

## Classification (all 12)

Detail moved to [`../notes/155-red-drift.md`](docs/plan/notes/155-red-drift.md).

**Your lane's block (`WIP`, ftc, 2026-08-27).** Four declarations landed, every
one accepted by `Kernel::add_declaration` on the first attempt and axiom-free:
`integral_abs_le_of_bound`, `integral_sub_linear_le`, `antiderivative`,
`antiderivative_abs_le`. Rung 3 (`HasDerivativeOn G F a b`) is characterised
with a route and **three named lemmas, none of them an estimate**.

**The sizing was right in shape and wrong in two of three citations, both in the
cheaper direction.** `integral_abs_le` CANNOT supply the bound: its right-hand
side is `mag_bound k = k+1`, never smaller than one, while FTC needs
`1/(e+1)`. The composition is with that lemma's ROUTE (`integral_le` +
`integral_const` against `±M`), not its statement — which is why
`integral_abs_le_of_bound` had to be declared at all. And `integral_scale` is
not needed anywhere: the `−F(z)` leg is a constant FUNCTION, so `integral_const`
evaluates it exactly.

**Where the cheap route was found: one level DOWN, not up.** Asking "which
algebraic operation is this?" gives scaling by −1 and reaches for
`integral_scale`. Asking "which integrand is this?" gives a constant, and the
dependency disappears. The standing lesson has been "ask at several levels of
abstraction"; this refines it — the useful direction was toward the concrete.

**The undecidable-order obstruction is removable without a case split.** With
`m := min x y` as a common base point, both legs are `integral_sub_linear_le` at
base `x`, and `A − B = G(y) − G(x) − F(x)(y−x)` with
`|A−B| ≤ ε·(max x y − m) = ε·|y−x|`. No decidable comparison is needed.

**What rung 3 still needs, none of it an estimate:**

1. `integral_split_arbitrary` **without** its `PosBound` — FTC applies it at
   `[a, clamp y]`, whose width is zero at `y = a`. The route is `lt_cotrans`
   against a shrinking `δ`, degenerate branch discharged by `integral_abs_le` on
   all three legs, both branches feeding one `equiv_zero_of_small`. This is the
   route `integral_abs_le`'s own doc names and nobody has run.
2. Clamp monotonicity: `le p q → le (max a (min p b)) (max a (min q b))`.
   Absent from `creal/`.
3. `Equiv (add (max x y) (neg (min x y))) (abs (add y (neg x)))` — `max − min`
   is the absolute difference. `max_congr`, `min_congr`, `min_le_left`,
   `le_min`, `max_le` and `abs_add_le` all exist; no `max_sub_min` does.

Detail moved to [`../notes/157-ftc.md`](docs/plan/notes/157-ftc.md).

**Your lane's block (`DONE`, ftc-rung3, 2026-08-27). FTC-I is landed.**
`CReal.hasDerivative_antiderivative : ∀ F a b (hab : le a b)
(u : UniformlyContinuousOn F a b) (kb : Nat), BoundedOn F a b kb →
HasDerivativeOn (antiderivative F a b hab u) F a b` — accepted by
`Kernel::add_declaration` on the **first attempt**, axiom-free, together with
the four lemmas it needed. Six declarations, six first-attempt accepts, and
the kernel rejected **nothing** in this lane.

| declaration | statement |
| --- | --- |
| `CReal.min_mono_left` | `∀ x y b, le x y → le (min x b) (min y b)` |
| `CReal.max_mono_right` | `∀ a u v, le u v → le (max a u) (max a v)` |
| `CReal.clamp_mono` | `∀ a b x y, le x y → le (max a (min x b)) (max a (min y b))` |
| `CReal.clamp_id` | `∀ a b x, le a x → le x b → Equiv (max a (min x b)) x` |
| `CReal.max_sub_min` | `∀ x y, Equiv (add (max x y) (neg (min x y))) (abs (add y (neg x)))` |
| `CReal.integralSplitAnywhere` | `integral_split_arbitrary` with its `PosBound` and `k` removed |
| `CReal.hasDerivative_antiderivative` | FTC-I, above |

**All three named lemmas were genuinely absent**, re-verified against
`creal.rs`'s name registry — the authoritative interning site, since every
`CReal.*` name is a `kernel.name_str(creal, …)` there and grep across
`crates/axeyum-lean-kernel/src/` finds no other. The lattice surface was
exactly the six order laws and three congruences: no monotonicity lemma, no
`max_sub_min`.

**The sizing missed a FOURTH lemma, and it was hiding place 2.** The spec's
error term is `F(x)·(y − x)` in the RAW `x`, `y`, while `G`'s argument is the
clamp, so the clamp must be shown to be the identity on `[a, b]`. That fact
existed as `derivative.rs`'s **private Rust helper**
`clamp_into_equiv_on_interval` — never a declaration, so no proof term could
cite it, and no name search could find it. It is now
`CReal.clamp_id`.

Detail moved to [`../notes/158-ftc-rung3.md`](docs/plan/notes/158-ftc-rung3.md).

**Status: PARTIAL — the keystone landed, the target did not, and the gap is
now precisely sized.** 2026-08-27.

The target itself is NOT landed and nothing here should be read as implying
π. What landed is the one missing analytic fact standing under it.

**The searched question, answered.** A "uniform limit of derivatives" theorem
is **genuinely absent** from this development. Measured against a FRESH
`shape_search` index (`declarations=1889`, matching the current tree, so the
stale-prebuilt false-ABSENT hazard does not apply):

- `--concl CReal.HasDerivativeOn` → **FOUND 16**, and all sixteen are
  pointwise combinators (`mk`, `const`, `id`, `sq`, `neg`, `add`, `sub`,
  `smul`, `mul`, `pow`, `pow_two`, `cube`, `chain`, `chain_id_sq`, `congr`,
  `integral_const`). Not one takes a limit hypothesis.
- `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn` → **ABSENT**
  (exit 1, positive control `any-kind=1889 ns CReal=512`).
- `--hyp CReal.UniformConvergesOn` → **FOUND 5**: `.rate`, `.rec`, `.spec`,
  `uniform_converges_add`, and `uniform_limit_uniformly_continuous`. The
  last is the ONLY theorem in the tree that transports any property at all
  through a uniform limit.

**The finite-partial-sum route does not avoid the interchange.** Writing `Sₙ`
for a partial sum and `F` for its uniform limit, the standard split is
`(A) |(F y − F x) − (Sₙ y − Sₙ x)| + (B) |(Sₙ y − Sₙ x) − Sₙ'(x)(y−x)| +
(C) |Sₙ'(x) − F'(x)|·|y−x|`. (B) is each partial sum's own `spec`; (C) is
uniform convergence of the derivative series, which `sinFnUniformConverges`
already supplies. (A) is bounded by uniform convergence of the FUNCTIONS only
by a **constant** `2δₙ`, while `deriv_spec_body`'s budget is
`(1/(e+1))·|y − x|` quantified over every `y` within `1/(m e + 1)` of `x` —
including points arbitrarily close to it. No `n` absorbs a constant into an
`ε·|y − x|` budget, so the interchange is required by the shape of the spec,
not by how the limit happens to be taken.

Detail moved to [`../notes/159-cos-deriv.md`](docs/plan/notes/159-cos-deriv.md).

**Done (`WIP`, absence-adopt, 2026-08-27).** ADR-0611 / `scripts/check-absence-claims.py`
landed with adoption printed on every run: **4/145 checkable claim sites
marked** (per `docs/plan/status/151-absence-expiry.md`). This lane worked
through the 141 checkable-but-unmarked `docs/` sites by hand — not a sweep —
to raise coverage honestly and find stale claims, since a partial rollout is
exactly the defect ADR-0611 exists to prevent one level up.

**Census before (this lane's first run, fresh `--release` authority):**

```
authority: 1889 distinct kernel declarations (floor 1750)
scanned: 4000 files
markers: 5 (1 absent, 4 was-absent), naming 9 declaration(s); 10 more QUOTED
census: 709 absence-claim site(s); 146 name a declaration (4 carry a marker,
  142 do NOT); 563 name no declaration and are STRUCTURALLY UNCHECKABLE
FAIL: 142 unexpirable absence claim(s) naming a declaration, over the budget
  of 141 (concurrent `crates/` lanes had already pushed the bare-named count
  one over budget before this lane touched anything)
```

**Census after:**

```
markers: 20 (9 absent, 11 was-absent), naming 40 declaration(s); 10 more QUOTED
census: 710 absence-claim site(s); 147 name a declaration (18 carry a marker,
  129 do NOT); 563 name no declaration and are STRUCTURALLY UNCHECKABLE
OK: 20 marker(s) checked against the kernel; every claim still holds.
  Marker coverage of checkable claim sites: 18/147.
```

Detail moved to [`../notes/160-absence-adopt.md`](docs/plan/notes/160-absence-adopt.md).

**Done for this session (inverse-fn, 2026-08-27).** First job was
establishing state, since `creal/inverse.rs` and `creal/inverse_fn.rs` are not
what their names suggest and the chapter's status was not written down
anywhere reliable.

**`creal/inverse.rs` (1,137 lines) is unrelated to the inverse FUNCTION
theorem.** It is `CReal.inv` — the multiplicative (field) reciprocal
`1/x` — with its shift/index/congruence plumbing and
`declare_mul_inv_cancel`/`declare_inv_congr`/`declare_inv_index_irrelevant`.
Nothing there was touched.

**`creal/inverse_fn.rs` already carried one landed theorem before this
session**, and it was landed on `main` (commit `94160585a`,
2026-08-26 — a day before this session started, not this session's work):
`CReal.order_reflect_of_pos_deriv`, the order-reflecting converse of
`strict_mono_of_pos_deriv`, conditional on a given `Apart x y`. Its own module
doc already explains why UNCONDITIONAL order-reflection is out of reach
(deciding `x<y` vs `y<x` from a codomain fact alone is IVT-exact-preimage
territory, and `ivt_approx` is still open) and why the `Apart`-conditional
form is exactly what Chapter 12 needs to compose with
`strict_injective_of_pos_deriv`. Also already landed (commit `7156f5304`,
same day, in `monotone.rs`, not `inverse_fn.rs`):
`CReal.inverse_lipschitz_of_pos_deriv`, the CONTINUITY-of-the-inverse
statement (`Apart x y → |x−y| ≤ (2k+2)·|Fx−Fy|`), built by the same
case-split-on-given-`Apart` idiom. So of the brief's three plausible
rungs, **rung 1 (continuity on the image interval) was already done**
before this session, by a prior lane, and needed no further work — it is
exactly what `inverse_lipschitz_of_pos_deriv` states.

**This session landed rung 2: `CReal.ivt_exact_root_at`** — existence of the
inverse as a function:

```
CReal.ivt_exact_root_at :
  ∀ F F' a b, HasDerivativeOn F F' a b →
  UniformlyContinuousOn F a b → le a b →
  ∀ y, le (F a) y → le y (F b) →
  ∀ k, (∀ z, le a z → le z b → le (ofRat (natDivSucc 1 k)) (F' z)) →
  ∃ c, le a c ∧ (le c b ∧ Equiv (F c) y)
```

Detail moved to [`../notes/161-inverse-fn.md`](docs/plan/notes/161-inverse-fn.md).

**Status: LANDED — `CReal.hasDerivative_uniform_limit` is admitted,
axiom-free, and the query that measured its absence now returns it.**
2026-08-27.

The target, verbatim from the source (`creal/uniform_convergence.rs`):

    CReal.hasDerivative_uniform_limit :
      ∀ (F F' : Nat → CReal → CReal) (G G' : CReal → CReal) (a b : CReal),
        (∀ n : Nat, HasDerivativeOn (F n) (F' n) a b) →
        UniformConvergesOn F G a b →
        UniformConvergesOn F' G' a b →
        HasDerivativeOn G G' a b

Through `Kernel::add_declaration` (the only trust anchor), on the first
attempt, with `axiom_footprint` **0** in all three preludes that build it
(`creal`, `complex`, `cpoint`).

**Re-verified before building, and again after.** Against a freshly built
`shape_search`, `--concl CReal.HasDerivativeOn --hyp CReal.UniformConvergesOn`
was **ABSENT (exit 1)** at `declarations=1890` and is now **FOUND 1** at
`declarations=1893` — exactly the three theorems below, no others. The
sixteen pre-existing `HasDerivativeOn` conclusions are unchanged and were all
pointwise combinators; this is the first that takes a limit hypothesis.

**Three declarations, not one, and the middle one is the finding.**

1. `CReal.lipschitz_of_deriv_bound` — `abs_diff_le_of_deriv_bound` with its
   endpoints **UNORDERED**:

       ∀ F F' a b, HasDerivativeOn F F' a b → ∀ M, le zero M →
       (∀ z, le a z → le z b → le (abs (F' z)) M) → ∀ x y,
       le a x → le x b → le a y → le y b →
       le (abs (add (F y) (neg (F x)))) (mul M (abs (add y (neg x))))

Detail moved to [`../notes/162-uniform-deriv.md`](docs/plan/notes/162-uniform-deriv.md).

**Your lane's block (`DONE for this slice`, ratint, 2026-08-27).**

**State before this lane, established by reading `ratint.rs` first (it had
zero tests and no doc note anywhere else pointing at it):** the *producer*
side of rational-function integration already existed, further along than
the task brief assumed. `crates/axeyum-cas/src/ratint.rs` already had
`horowitz` (Horowitz–Ostrogradsky rung 1, the rational part) AND
`rothstein_trager_resultant` / `rational_roots` / `log_terms` (Rothstein–
Trager rung 2, the logarithmic part). `lib.rs`'s public `integrate()` already
wires both into a certified antiderivative via the general CAS-wide
differentiate-and-compare route (`prove_derivative` / `equal`,
`CertifiedIntegral`), including a rung-3 path to `arctan` for irreducible
quadratics via `apart` + `integrate_partial_fraction_term`
(`integrate_log_part_by_factoring`). So the producer ladder in the task brief
was already climbed; what was missing was a **small, independent checker**
distinct from the CAS-wide `equal()` engine, and any tests at all for this
module.

**What landed:** two `pub(crate)` checkers in `ratint.rs`, `verify_horowitz`
and `verify_log_terms`, that re-derive correctness purely in `poly.rs`
exact-`Rational` arithmetic — never through `CasExpr`/`equal`. Both return
`Option<bool>` (`None` = internal overflow/decline, `Some(false)` =
rejected, `Some(true)` = every guard passed), matching the
`verify_partial_fraction_certificate` convention in `partial_fractions.rs`.
22 tests, all guards mutation-verified (delete the guard, confirm at least
one test dies; two guards found to be provably, always subsumed by another
were removed rather than kept as decoration, matching the partial-fractions
lane's own precedent — see the module doc and commit history for the
algebraic proof of each subsumption).

Detail moved to [`../notes/163-ratint.md`](docs/plan/notes/163-ratint.md).

**Your lane's block (`DONE`, ftc2, 2026-08-27). FTC-II is landed.**
`CReal.integral_eq_antideriv_diff : ∀ F G a b (hab : le a b)
(u : UniformlyContinuousOn F a b) (kb : Nat), BoundedOn F a b kb →
HasDerivativeOn G F a b →
Equiv (integral F a b hab u) (add (G b) (neg (G a)))` — accepted by
`Kernel::add_declaration` on the **first attempt**, axiom-free, together with
every helper it needed. The kernel rejected nothing in this lane.

**The route, as characterised in the brief, held exactly.** `A :=
antiderivative F a b hab u` (FTC-I's own construction) is ALSO an
antiderivative of `F` (`has_derivative_antiderivative`), so `D := fun r =>
G r − A r` has derivative `zero` everywhere on `[a, b]`
(`hasDerivative_sub` composed with `add_neg`), and `constant_of_zero_deriv`
gives `D a ~ D b`, i.e. `G a − A a ~ G b − A b`.

**`constant_of_zero_deriv`'s hypotheses matched the classical route
exactly**, no adjustment needed: `∀ F F' a b, HasDerivativeOn F F' a b →
(∀ z, le a z → le z b → Equiv (F' z) zero) → ∀ x y, le a x → le x y → le y
b → Equiv (F x) (F y)`. Applied at `x := a, y := b` (via `le_refl a`, `hab`,
`le_refl b`), it gives `D a ~ D b` directly.

**`∫ₐᵃ F ~ 0` DID need its own step, and it is the same step twice.**
`A a` is `integral F a (clamp a) …` where `clamp a := max a (min a b)`;
`clamp_id` gives `Equiv clamp_a a` (exact, not merely epsilon-close), so the
interval's width is `Equiv`-zero and `integral_abs_le` bounds `|A a| ≤ M·0
~ 0`. Symmetrically, `A b`'s relationship to `integral F a b hab u` needed
`integral_split_anywhere` at the split point `clamp b` (`clamp_id` again
gives `clamp b ~ b`), leaving a leading piece that IS `A b` and a trailing
piece `[clamp b, b]` that is degenerate by the SAME argument. Both
degenerate-interval facts are one shared helper,
`integral_zero_of_width_zero` — built once, called twice (leading and
trailing sides).

Detail moved to [`../notes/164-ftc2.md`](docs/plan/notes/164-ftc2.md).

**Your lane's block (`DONE for this pass`, cas-audit, 2026-08-27).** Censused
709 pub/pub(crate) fns across `crates/axeyum-cas/` (57 src files, excluding
test bodies) against ALL test evidence in the crate — in-file `#[cfg(test)]`
blocks, `tests/*.rs`, `examples/*.rs`, and (checked separately, by hand)
subprocess-driven `bin/*` CLI tests and the `scripts/check-sos-negative-controls.sh`
shell-fixture suite, none of which a plain grep sees. A naive per-file
`#[cfg(test)]`-presence check flags ~72 candidates; cross-referencing every
file's test block (not just its own) against every name drops that to 45; manually
resolving each of those 45 found that nearly all are exercised indirectly
(mvpoly's Groebner primitives via Buchberger's-criterion self-checks in
`groebner.rs`, `ratint.rs`'s `rothstein_trager_resultant` via `log_terms`'s
tests, the SOS checkers via 36 assertions over 21 negative-control fixtures —
confirmed still green this session, `21 negative control fixture(s), 36
assertion(s) run, 0 failure(s)`).

Detail moved to [`../notes/165-cas-audit.md`](docs/plan/notes/165-cas-audit.md).

**Status: LANDED — the target is admitted.**
`CReal.cosFnWideHasDerivative : HasDerivativeOn cosFnWide (fun x => neg (sinFn
x)) zero (ofRat (Rat.natDivSucc 8 4))` is through
`Kernel::add_declaration`, axiom-free, and **cosine differentiates to minus
sine on `[0, 8/5]`** in this kernel. 2026-08-27.

Detail moved to [`../notes/166-cos-deriv2.md`](docs/plan/notes/166-cos-deriv2.md).

**Your lane's block (`DONE`, intparts, 2026-08-27).** Integration by parts is
landed. `CReal.integral_by_parts : ∀ u u' v v' a b (hab : le a b),
HasDerivativeOn u u' a b → HasDerivativeOn v v' a b →
UniformlyContinuousOn u a b → UniformlyContinuousOn u' a b →
UniformlyContinuousOn v a b → UniformlyContinuousOn v' a b →
Equiv (integral (fun r => mul (u' r) (v r)) a b hab ‹u'v witness›)
      (add (add (mul (u b) (v b)) (neg (mul (u a) (v a))))
           (neg (integral (fun r => mul (u r) (v' r)) a b hab ‹uv' witness›)))`
— accepted by `Kernel::add_declaration` on the **second attempt** (one real
bug, see below), axiom-free.

**Route, exactly as the brief characterised.** `has_derivative_mul` gives
`(uv)' = u'v + uv'`. `BoundedOn` witnesses for `u`, `u'`, `v`, `v'` are
derived from the four `UniformlyContinuousOn` hypotheses via
`bounded_of_uniformly_continuous` (**not** taken as independent hypotheses
the way `hasDerivative_cube`/`hasDerivative_mul` itself does — here they are
all cheap since the theorem already assumes uniform continuity of all four
functions). FTC-II (`integral_eq_antideriv_diff`) applied to `u*v` gives
`∫(u'v+uv') = u(b)v(b) − u(a)v(a)`; `integral_add` splits the left side into
`∫u'v + ∫uv'`; the final rearrangement `I1 + I2 ~ D ⟹ I1 ~ D − I2` reuses
`integral.rs`'s own private `add_cancel_right` (already built for FTC-II's
own closing step — no new algebra lemma needed). Every gap between a
hand-built lambda (`u'v`, `uv'`, `u'v+uv'`, `u*v`) and the shape a
combinator's own conclusion produces is a pure beta redex, bridged via
`echain` relying on the kernel's defeq check — the same technique FTC-II's
own `h_dab` bridge uses.

Detail moved to [`../notes/166-intparts.md`](docs/plan/notes/166-intparts.md).

**Your lane's block (`WIP`, supon5, 2026-08-27).** Rung 5 of `supOn`'s route
2 (nested-refinement) landed: `CReal.expOfModulus`/`CReal.trueExpOfModulus`,
the accuracy-selection schedule the module doc's plan called for, all
five declarations kernel-verified first-attempt. `supOn` itself (rungs
6-7: telescope via `sumRange_cauchy_of_dominated` against a concrete
ratio-1/2 geometric dominator, then `regular_of_scaled_cauchy` -> `CReal.mk`)
is **not** landed this pass — see `creal/supremum.rs`'s own module doc,
which now records rung 5 as done and rungs 6-7 as the next concrete task,
same characterization as before this session (unchanged; not re-verified
against rung 5's actual construction).

What landed, precisely:
- `CReal.expOfModulus : (Nat -> Nat) -> Nat -> Nat := fun m k => Nat.size (m
  (meshLevelCount k))` — generic over the modulus `m` rather than tied to a
  specific `UniformlyContinuousOn` witness (callers apply it at `m :=
  UniformlyContinuousOn.modulus F a b u`).
- `CReal.trueExpOfModulus : (Nat -> Nat) -> Nat -> Nat`, `Nat.rec`-structured,
  `trueExpOfModulus m 0 := expOfModulus m 0`, `trueExpOfModulus m (succ k) :=
  add (trueExpOfModulus m k) (expOfModulus m (succ k))` — built with
  `Nat.add` (this kernel's `Nat` prelude has no `Nat.max`), plus its two
  defining equations (`_zero`, `_succ`, both `Eq.refl`).
- `CReal.trueExpOfModulus_step_le` (adjacent step, `Nat.le_add_right`
  directly, defeq to the `_succ` equation's RHS) and `_mono` (general
  monotonicity via `Nat.monotone_of_le_succ`, the `Nat`-level twin of
  `CRealPrelude::mono_of_le_succ`, exactly `meshMax_mono`'s own
  construction one type down).
- `CReal.expOfModulus_le_trueExpOfModulus : forall m k, Nat.le (expOfModulus
  m k) (trueExpOfModulus m k)` — the accumulator is always at least as fine
  as the single level it covers; needed by rung 6. Proved by `NatOps::induct`
  (mirrors `declare_max_range_self_le`); the step case needs `Nat.le_add_right`
  read through `Nat.add_comm` via `rat_prelude::ops::nat_rewrite_prop`, since
  this kernel's `Nat` prelude has no `Nat.le_add_left`.

Detail moved to [`../notes/168-supon5.md`](docs/plan/notes/168-supon5.md).

**Status: RUNG 1 LANDED, π NOT LANDED, and the two remaining rungs are sized
with measured numbers rather than guesses (pi, 2026-08-27).**

Four things went through `Kernel::add_declaration`, all axiom-free, **all
accepted on the first attempt — the kernel rejected nothing in this lane**:

    CReal.cosFnWide_one_equiv_cosOne : Equiv (cosFnWide one) cosOne
    CReal.cosFnWide_one_nonneg       : le zero (cosFnWide one)
    CReal.hasDerivativeOn_restrict   :
      ∀ F F' a b a' b', HasDerivativeOn F F' a b →
        le a a' → le a' b' → le b' b → HasDerivativeOn F F' a' b'

plus one test, `cos_fn_wide_at_one_and_the_derivative_restriction_state_what_
pi_needs`, which pins those statements structurally and **instantiates the
restriction at the real interval**: `HasDerivativeOn cosFnWide (fun x => neg
(sinFn x)) one (8/5)` is a term this kernel accepts today.

**π is not constructed and no root is asserted to exist.** What landed is the
LEFT endpoint of the sub-interval and the interval-narrowing lemma. Rungs 2
and 3 below are unproved, here and everywhere in this tree.

## Rung 1: `cos 1 ≥ 0` — and why `CReal.cosOne_nonneg` was not already it

`CReal.cosOne_nonneg : le zero cosOne` has existed since the `cosOne`
alternating-bound work. It says nothing about `cosFnWide`, because `cosOne`
is `creal/trig.rs`'s single CONSTANT (the limit of `sumRange cosTerm`) and
`cosFnWide` is `weierstrassMTest`'s uniform limit `G` on `[0, 8/5]` — and
`CReal.cosFn_one_equiv_cosOne`, the only bridge in the tree, is about the
NARROW `cosFn` on `[0, 1]`, a different declaration on a different interval.
Nothing relates two uniform limits pointwise without an argument.

Detail and older landed rows moved to [`../notes/169-pi.md`](docs/plan/notes/169-pi.md).

**Your lane's block (`WIP`, supon6, 2026-08-27).** No new kernel
declarations landed this pass. What landed is a corrected module-doc map of
`creal/supremum.rs`'s rung 6 — the coordinator's brief flagged the existing
sketch as written by a lane that "did not attempt it" and asked to treat it
as a hypothesis; it does not hold up, and the doc now says precisely why,
with two named candidate routes for whoever attempts rung 6 next.

**The "constant-multiple corollary" the old sketch names as the one open
piece is not the bottleneck.** It already exists in substance:
`geometric.rs`/`exponential.rs`/`trig.rs`'s `pub(super)`
`mul_ordered_half_body` + `promote_ordered_half_to_full` +
`telescope_cauchy_pad2` already scale an ordered-half Cauchy bound by a
fixed positive `CReal` constant and promote it past `Nat.le_total`, and
`CReal.cauchy_of_abs_diff_le` (`creal/ivt.rs`) already supplies the general
real-bound-to-canonical-sample bridge `regular_of_scaled_cauchy` needs, with
a RAW `(K, proof)` pair available from its own construction (the body,
before the final `cexists_intro`) — this development's standing convention
is to reproduce a sibling's private helper rather than widen its visibility
for one caller, so this is a reproduction task, not a derivation.

Detail moved to [`../notes/170-supon6.md`](docs/plan/notes/170-supon6.md).

**Status: LANDED and kernel-accepted (`DONE`, pi-rung3, 2026-08-28).**

`CReal.sinFnLowerBoundOneToR : ∀ z, le one z → le z (ofRat (natDivSucc 8 4))
→ le (ofRat (natDivSucc 1 3)) (sinFn z)` — pi rung 3
(`docs/plan/status/169-pi.md`'s own sizing): a uniform lower bound
`sin z ≥ 1/4` on `[1, 8/5]`. Confirmed by
`existing_step_order_is_topologically_valid` (~97–99 s across three runs,
`test result: ok`), which builds the FULL prelude through
`Kernel::add_declaration` — the trusted gate, not a syntactic check.

**The 169-pi.md arithmetic checked out exactly as sized**, verified before
building anything: `119·4 = 476 ≥ 375·1 = 375` (`119/375 ≥ 1/4`); the
antitonicity chain `z² ≤ 64/25 ≤ 6 ≤ (2k+2)(2k+3)` for every `k ≥ 0`
(minimum of the RHS is `2·3 = 6` at `k = 0`); `k := 3` is the correct
constant (`natDivSucc 1 3 = 1/4`). No shift is needed, unlike cosine's own
`8/5` bound (rung 2) — sine's magnitude sequence is globally antitone on
this domain.

Detail moved to [`../notes/172-pi-rung3.md`](docs/plan/notes/172-pi-rung3.md).

**Status: THE BOUND DID NOT LAND. Two general theorems that rung 2 needs, and
that nothing in the tree had, DID — and the route `169-pi.md` proposed is
not the one that works (pi-rung2, 2026-08-27).**

Landed, axiom-free, both accepted by `Kernel::add_declaration`:

    CReal.converges_upper_bound_shift :
      ∀ s f L b, (∀ n, le (f (Nat.add n s)) b) → Converges f L → le L b

    CReal.alternatingUpperBoundTail :
      ∀ a, (∀ k, le zero (a k)) → (∀ k, le (a (succ (succ k))) (a (succ k))) →
        ∀ L, Converges (sumRange t) L → le L (sumRange t 3)
      where t j := mul (pow (neg one) j) (a j)

`le (cosFnWide (ofRat (natDivSucc 8 4))) zero` is **not proved**, here or
anywhere in this tree, and no root of cosine is asserted to exist.

## The arithmetic, re-verified independently of the brief

- `a k := (8/5)^{2k}/(2k)!`; `a 0 = 1`, `a 1 = 32/25 = 1.28`,
  `a 2 = (4096/625)/24 = 512/1875 ≈ 0.27307`. `a 1 > a 0`, so the GLOBAL
  antitonicity `alternatingLowerBound`/`alternatingUpperBound` demand fails at
  `k = 0`, exactly as `169-pi.md` measured.
- `a 1 − a 2 = 2400/1875 − 512/1875 = 1888/1875 ≈ 1.006933`; margin over `1` is
  `13/1875 ≈ 0.006933`. Both confirmed.
- **The same margin reads more usefully off the ODD partial sum.**
  `O 1 = a 0 − a 1 + a 2 = 1 − 32/25 + 512/1875 = −13/1875 < 0`, and
  `cos(8/5) ≈ −0.0292 ≤ −13/1875`. That is the same number the brief's
  `1 − 1888/1875` produces, and it is a statement about `a`'s OWN partial
  sums rather than about a shifted series' limit — which is what made the
  route below possible.

Detail and older landed rows moved to [`../notes/174-pi-rung2.md`](docs/plan/notes/174-pi-rung2.md).

**Status: items 1-2 of `docs/plan/status/174-pi-rung2.md`'s four-item list
LANDED, axiom-free. Items 3-4 (the `Converges` witness and the numeric
evaluation) are NOT built, and are characterised as a genuinely new,
substantial undertaking — see below (pi-r2b, 2026-08-28).**

Detail moved to [`../notes/175-pi-r2b.md`](docs/plan/notes/175-pi-r2b.md).

**Status: LANDED, axiom-free, accepted by `Kernel::add_declaration` on the
FIRST attempt (cw-bridge, 2026-08-28).** The bridge
`docs/plan/status/175-pi-r2b.md` named as the last structural gap under π
rung 2 exists and is public:

    CReal.converges_of_abs_diff_le :
      ∀ (f : Nat → CReal) (L : CReal) (K : Nat),
        (∀ n, CReal.le (CReal.abs (CReal.add (f n) (CReal.neg L)))
                       (CReal.ofRat (Rat.natDivSucc K n)))
        → CReal.Converges f L

`crates/axeyum-lean-kernel/src/creal/uniform_convergence.rs`. Read from the
kernel, not from source text: `shape_search --include-constructed --name
CReal.converges_of_abs_diff_le` gives `theorem arity=4 CReal -> CReal -> Nat
-> CReal.le -> CReal.Converges`, `consts=[CReal, CReal.Converges, CReal.abs,
CReal.add, CReal.le, CReal.neg, CReal.ofRat, Nat, Rat.natDivSucc]`, and
`prelude_theorem_inventory --include-constructed --release` prints
`creal  CReal.converges_of_abs_diff_le  0` — zero axioms.

## Was it genuinely absent? Yes — but the HARD half was not

Verified before building, not assumed. `shape_search --concl
CReal.Converges` returned 13 rows and not one takes a `CReal.le`-of-`abs`
hypothesis (`converges_of_close` and `converges_of_scaled_cauchy` both start
from a `Within`; `converges_of_equiv` wants exact `Equiv`;
`converges_squeeze` wants two existing `Converges`). `--name-like
close_within` returned exactly `close_within_of_within` and
`close_within_of_within_indexed`, both concluding `CReal.le` — the OTHER
direction. Grepped `within_of_two_sided_le`'s consumers and every
`close_within` site in `creal/` for an inline instance (hiding place 2); the
one that exists is `creal/ivt.rs`, and it is the Cauchy analogue, not this.

**But 175-pi-r2b's sizing — "a THIRD general bridge, comparable in size to
`converges_add`'s own construction … relating a real's sample at `n` to its
sample at `shift n`" — over-stated the work, and the reason is worth
recording because it is hiding place 1 again.** The `CReal.add` index-shift
regularity bridge ALREADY EXISTS as a general, public lemma:

Detail moved to [`../notes/176-cw-bridge.md`](docs/plan/notes/176-cw-bridge.md).

**Your lane's block (`DONE`, inline-hunt, 2026-08-28).** Censused ~426
`declare_*` functions and ranked ~333 private-fn candidates (body_len>=25)
across every in-scope `creal/` file, using: theorem-shaped `///` doc
comments on private (non-`declare_`) fns, "does not exist"/"not landed"
comments, structuring comments ("self-contained", "independently useful"),
and a body-length + call-site ranking script. Result: **every strong hit
this session's signals surfaced (clamp_id, bucketClose,
converges_upper_bound_shift, hasDerivative_closeOfEquiv,
congr_of_uniformly_continuous, uniformly_continuous_mul) was already
extracted by other lanes earlier today** — this campaign has been running
hard enough that the obvious hiding-place-2 instances are largely cleared.

What this lane actually landed instead: `CReal.abs_add_le` has been a
public kernel declaration (`uniform_continuity::declare_abs_add_le`) for a
while, but `series.rs`, `derivative.rs` (7 call sites) and
`deriv_unique.rs` (1 call site) each still carried a private
proof-term-rebuilding copy, and `uniform_continuity.rs` itself re-derived
it twice more beyond its own declaration's proof. All 10 call sites now
cite `d.lemma(p.abs_add_le, &[a, b])`; the 3 now-dead private copies
(`series.rs`'s also took its now-unused `neg_add` with it) are gone.
Also fixed a stale doc comment in `derivative.rs` (`hasDerivative_pow`)
claiming `uniformly_continuous_mul` "does not exist" — it has, publicly,
since `fb2c703a6`.

Verification: clean `cargo check`/`clippy -D warnings`;
`creal_prelude_builds` 94.01s (within the recent 94-123s band, no
regression); `every_creal_declaration_is_checked_and_axiom_free` passes
`--release` (declaration count unchanged — no new declarations, only
duplicate private builders removed).

**No new kernel declaration was extracted.** I did not find a genuinely
general, previously-un-named inline step within budget that clearly
warranted one — several large private fns ranked highly by the body-length
signal (e.g. `integral.rs`'s `bnd_leg_plus_share_le`, 161 lines / 13 call
sites) turned out to be tightly coupled to one declaration's own internal
plumbing (named parameters like `bound_at_idx`, `idx`, `m` specific to that
construction) rather than general facts another module would search for.
Next lane: the census signals that worked are logged in this session's
transcript; the remaining un-swept files are the largest ones
(`integral.rs` 29.5k lines, `derivative.rs`, `monotone.rs`, `ivt.rs`) —
worth another pass with fresh eyes rather than repeating my grep signals,
which are now mostly exhausted against what remains.

**Your lane's block (`DONE`, rs-cauchy, 2026-08-28).** No code changes: the
whole task was already landed on `main` before this lane started, 35 commits
back at `590925680` (`feat(creal): CReal.integral_by_parts`).

Task brief: build `riemannSum_cauchy`, predicted to be the literal
`CReal.Cauchy (fun m => riemannSum F a b m)` member of the family, supplied
by `CReal.cauchy_of_abs_diff_le` (landed today in `creal/ivt.rs` for the IVT
root). That prediction did not hold, but the underlying goal — closing the
`riemannSum` roadmap through `CReal.integral` — is done, by a different,
already-integrated route:

- `CReal.riemannSum_cauchy` (`integral.rs`, `declare_riemann_sum_cauchy`) is
  the **`Within`-bound**, shared-index closeness statement (roadmap step 5),
  explicitly documented as NOT the literal `CReal.Cauchy` shape.
- The literal-Cauchy-*rate* shape needed to build `CReal.integral` is instead
  `CReal.riemannSumDeepCauchyFolded` (`declare_riemann_sum_deep_cauchy_folded`),
  reached via re-indexing (`deep`) rather than via `cauchy_of_abs_diff_le` —
  `cauchy_of_abs_diff_le` is used only in `creal/ivt.rs` (its own consumer),
  never in `integral.rs` (confirmed by grep).
- `CReal.integral` itself (`declare_creal_integral`) is built from
  `regular_of_scaled_cauchy` fed that folded witness, and the whole chapter
  continues past it — `integral_converges`, `integral_const`,
  `integral_witness_independent`, `integral_add`, `integral_le`,
  `integral_scale`, `integral_split` (+ split_arbitrary/split_exact/
  split_scale_invariant/congr_of_uniformly_continuous), `integral_abs_le`,
  `ftc_estimates`, `integral_eq_antideriv_diff`, and
  `integral_by_parts` — all present in `EXPECTED_STEP_ORDER`
  (`creal_tests.rs`) and all axiom-free.

So: **the note that prompted this lane's brief was accurate about the
`cauchy_of_abs_diff_le` lemma existing, but the roadmap it named a gap in had
already been closed by the time this lane read it — by a different technique,
not the one predicted.** This is a precisely-sized negative: nothing was
missing to build, only stale to re-verify.

Detail moved to [`../notes/179-rs-cauchy.md`](docs/plan/notes/179-rs-cauchy.md).

**Your lane's block (`WIP`, pi-r2d, 2026-08-28).** Re-implemented items 3-4
after `a313345bf`'s revert (pi-r2c's attempt hit 616s/5.9GB and climbing on
`creal_prelude_builds`, killed). Item 3 (`CReal.cosWideSeriesConverges`) is
byte-identical to the reverted code — it already used
`CReal.converges_of_abs_diff_le`, which now exists (landed by the `cw-bridge`
lane after `pi-r2b` characterised item 3 as blocked on it). Item 4
(`CReal.cosWideNonpositive`) is rewritten: instead of feeding three natural,
multi-layer `Rat.mul`/`Rat.pow`/`Rat.normalize` towers straight into two
nested `Rat.add` calls (what the reverted attempt did), each term is first
collapsed to a flat, already-reduced `Rat.normalize` literal in ISOLATION
(one `Equiv.refl`-based def_eq check per term — `collapse_to_flat` in
`cos_sign.rs`), and only THEN combined via `Rat.add` in the order
`sumRange`'s own left-nested structure forces (`(0+t0)+t1)+t2`).

Detail moved to [`../notes/180-pi-r2d.md`](docs/plan/notes/180-pi-r2d.md).

**Your lane's block (`DONE`, pi-r2e, 2026-08-28).** π rung 2 is complete.
`CReal.cosWideSeriesConverges` (item 3) and `CReal.cosWideNonpositive :
le (cosFnWide R) zero`, `R := 8/5` (item 4) are both admitted by
`Kernel::add_declaration`, both axiom-free, and the prelude builds in band.

**Every number below was personally observed to completion** in this lane's
own worktree, debug profile, `RUST_MIN_STACK` unset (confirmed with
`printenv`, not assumed — see `CLAUDE.md`'s ambient-variable entry):

| tree | `creal_prelude_builds` | kernel |
| --- | --- | --- |
| baseline (merged `main`) | **100.65 s** | — |
| + item 3 only (`faff69a53`) | **101.22 s** | accepted |
| + item 4, first construction (`797100410`) | **587.02 s** | accepted |
| + item 4, bounded construction (`0f5f653a8`) | **113.46 s** | accepted |

Detail moved to [`../notes/181-pi-r2e.md`](docs/plan/notes/181-pi-r2e.md).

**Rung 6's gap bound LANDED (supon-r6, 2026-08-28).** Three declarations,
each a first-attempt kernel accept, all axiom-free and covered by
`creal_tests::every_creal_declaration_is_checked_and_axiom_free` (which reads
the environment, not a list):

- `CReal.meshPoint_near_coarse` — the **multi-level nearest-mesh-point
  lemma**, the piece nothing in the tree had. Every level-`(j+d)` mesh point,
  at *any* refinement depth `d`, sits in one level-`j` cell: between that
  cell's left endpoint and one coarse width above it.
- `CReal.maxRange_le_add_of_exists` — `maxRange_transport` restated to take an
  `eps`-estimate instead of an `Equiv`, and an `Exists` **witness** instead of
  a supplied index function `e : Nat -> Nat`.
- `CReal.meshMax_le_add_of_step_close` — **the gap bound**:
  `le (meshMax F a b (Nat.add j d)) (add (meshMax F a b j) eps)` at arbitrary
  depth, from a one-sided pointwise hypothesis on `F`.

**The `creal/supremum.rs` module doc's "Rung 6 re-verified (2026-08-27)"
section was right about WHAT blocks rung 6 and wrong about why it is
expensive.** Its diagnosis held up exactly: the blocker is the per-level gap
bound; `trueExpOfModulus` really can jump the mesh level by arbitrarily many
doublings; a nearest-coarse-point fact at *any* depth really is what that
needs. But it prices both candidate routes as "comparable in scope to a rung
of their own" because it assumes the coarse index must be **computed** — route
1 needs an index computation, route 2 needs a finer accuracy schedule.

Neither is true. The gap bound's conclusion is `Prop`, so the coarse index can
be an `Exists` witness that the induction step re-eliminates. Kernel fact 2
(`Exists.rec` is `Prop`-only) constrains rung 7's `CReal.mk`, where `K` and
`f_lambda` are DATA; it says nothing about a `le`-valued estimate. Once the
index is existential, "which coarse cell contains fine index `i'`" never has
to be answered: induct on depth and split the fine index's parity with
`Nat.even_or_odd`. No quotient/remainder algebra, no `bucketIndex`, no
schedule refinement — and `uniform_continuity.rs`'s still-open `crossingClose`
side condition is never touched, so nothing here imports that gap.

Detail moved to [`../notes/182-supon-r6.md`](docs/plan/notes/182-supon-r6.md).

**Your lane's block (`DONE`, choose-backlog, 2026-08-28).** All five targeted
facts landed as axiom-free kernel-lean proofs in
`crates/axeyum-lean-kernel/src/nat_prelude/choose.rs`:
`Nat.choose_one_right`, `Nat.choose_eq_zero_of_lt`, `Nat.choose_ne_zero`,
`Nat.choose_le_succ`, `Nat.choose_symm_of_eq_add`. `nat_prelude::` --lib went
94 -> 95 passed, 0 failed.

One real bug found and fixed along the way: `choose_le_succ`'s `c = 0` base
case assumed `choose(a, 0)` reduces to `1` by defeq for a SYMBOLIC `a` — it
does not (the outer recursor is stuck on a non-constructor first argument;
only `choose(succ a, 0)` reduces regardless of `a`). Caught by the full
`nat_prelude::` sweep (a single-test run against only that one theorem's own
test passed, then the full sweep failed with `TypeMismatch` across 95 tests
because the shared prelude build itself fails). Fixed by routing through
`choose_zero_right(a)` + `le_refl` instead of assuming defeq. Bisected by
toggling each of the five `declare_choose_*` calls in `declare_choose_all`
one at a time against the single fast test
`choose_computes_and_symm_holds_at_a_concrete_point`.

Also updated (both environment-derived, not hand-maintained lists per the
project's "every X must derive from the authority" rule):
`every_nat_declaration_is_checked_and_axiom_free`'s `theorem_names` list, and
`the_build_is_deterministic`'s rendered-declaration count pin
(`65+322` -> `65+327`, re-derived from the test's own failure message, not
guessed).

Fact ledger: all five `F:ml430-nat-choose-*` facts flipped `open` -> `proved`,
evidence mirrors `F:nat-choose-symm`'s pattern (`nat_theorem_inventory`
grep-count + `nat_axiom_inventory --require-axiom-free nat`), both checker
commands verified to discriminate (positive control passes, a fabricated
theorem name fails). `python3 scripts/validate-facts.py`: 1867 facts, 0
errors.

Nothing found already existing that the brief implied was missing — the
`choose.rs`/`binomial.rs` family cited in the brief (`declare_choose`,
`declare_choose_equations`, `declare_choose_self`, `declare_choose_symm`,
`sum_choose_row`, `choose_le_two_pow`, `succ_mul_choose_eq`) was exactly as
described, and none of the five target names existed anywhere in the tree
before this lane (grepped both spellings).

Detail moved to [`../notes/183-choose-backlog.md`](docs/plan/notes/183-choose-backlog.md).

**Your lane's block (`DONE`, coprime-backlog, 2026-08-28).** Landed four of
the five targeted facts with real, axiom-free kernel proofs (the brief's bar
was three). The fifth, `coprime_two_left` (`Coprime 2 n ↔ Odd n`), was not
attempted: `Odd` has no existing predicate anywhere in this prelude (grepped;
`Nat.even_or_odd` in `powsq.rs` is the closest primitive, giving a computed
half but no named `Odd`), so it needs a fresh `∃ k, n = 2*k+1` construction
plus a local `two_divisor_dichotomy`-style case split before the coprimality
argument even starts — sizeable enough on its own that it was not worth
risking the other four for. A future lane can lift `two_divisor_dichotomy`
straight from `irrational.rs` (already a local copy there, `perfect.rs`'s own
copy being `fn`-private) and build the `Odd` existential the same way `dvd`'s
own witness predicate is built (`NatOps::dvd_predicate`).

Landed, each a separate declaration in `crates/axeyum-lean-kernel/src/
nat_prelude/primes.rs` (new fields + build-order wiring in `nat_prelude.rs`,
registered in `nat_prelude_tests.rs`'s environment-derived `theorem_names`
so `every_nat_declaration_is_checked_and_axiom_free` covers them):

- `Nat.coprime_of_dvd_left : dvd a1 a2 → gcd a2 b = 1 → gcd a1 b = 1`
- `Nat.coprime_of_dvd_right : dvd b1 b2 → gcd a b2 = 1 → gcd a b1 = 1`
- `Nat.prime_dvd_iff_not_coprime : prime p → (dvd p n ↔ ¬(gcd p n = 1))`
- `Nat.coprime_add_self_right : gcd m (n+m) = 1 ↔ gcd m n = 1`

All four route through `Kernel::add_declaration` (real proof terms, not
assumed), rest on zero axioms (`nat_axiom_inventory --require-axiom-free
nat`: axiom=0 opaque=0 quotient=0), and are wired into
`fact-ledger F:ml430-nat-coprime-of-dvd-left-b0e2aa94`,
`F:ml430-nat-coprime-of-dvd-right-a640bd56`,
`F:ml430-nat-prime-dvd-iff-not-coprime-77854741`,
`F:ml430-nat-coprime-add-self-right-c3ed0f45` (now `proved`, `proof_route:
kernel-lean`, `formal.language: lean4` = actual `render_lean` output, not
the Mathlib surface text -- `Coprime`/`Prime` have no separate name in this
prelude, matching `coprime_of_lt_prime`'s established convention).

Detail moved to [`../notes/184-coprime-backlog.md`](docs/plan/notes/184-coprime-backlog.md).

**Your lane's block (`DONE`, decidable-frontier, 2026-08-28).** The brief named
three facts as the entire DECIDABLE-open frontier; only one of the three was
actually open.

- `F:rado-r4-a5-b3` and `F:rado-r4-a5-b4` were ALREADY SETTLED before this lane
  started (commits `04f480b52`, `061f8e634`/`b8be40096`) — `epistemic_status:
  computed`, evidence attached. `fact-frontier.py` prints "DECIDABLE --
  dispatch it" on their rows because that annotation is a fragment-routability
  label printed across several sections, not an open/closed signal — the rows
  sit under "ESTABLISHED HERE, NOT IN THE LITERATURE", not under an open
  section. Confirmed by re-running their own checkers here
  (`validate-claims.py`, `akb2_frontier verify`, `check-claim-certificates.py`
  — all 0 errors) and by `validate-facts.py`, which lists both under NOVEL.
  **Neither file was edited by this lane** (`git diff` on both is empty for
  the whole session).
- `F:fp16-add-monotone-rne` is the one genuinely open item, and it stays
  `open` — no evidence was added, only its `notes` gained a corroborating
  2026-08-28 re-measurement (decide-only reconfirmed at 11.09s unsat; search
  stage reconfirmed at 424,601 conflicts / ~24-27s / 827,048 proof steps /
  ~193MB; and NEW — a direct measurement of the checking stage's own
  throughput, previously known only as "doesn't finish in 3+ hours":
  `drat_check` runs ~95 steps/sec against 827,048 total steps, extrapolating
  to ~2.4h for that sub-stage alone before `elaborate_drat_to_lrat` even
  starts). `validate-facts.py` still reports 0 errors, `open=171` unchanged.
  A precisely measured obstruction, not a settlement.

**Your lane's block (`DONE`, evt-r2-gap, 2026-08-28).** The one labeled gap in
`creal/extreme_value.rs` (`evtLinear v` uniformly continuous — asserted, not
proved) is closed. All four pieces landed and are kernel-checked:

1. `CReal.abs_bound_of_self : ∀ x, le (abs x) (mag_bound (bound x))` —
   promoted from a private `fn` in `creal/uniform_continuity.rs` (unreachable
   outside that file) to a `CRealPrelude` field, closed over a fresh `fvar`.
   The sole prior call site (inside `declare_bounded_of_uniformly_continuous`)
   now calls `d.lemma(p.abs_bound_of_self, &[f_a])` instead of rebuilding the
   proof inline. Makes `BoundedOn` trivial for every constant function on
   every interval — not just `evtLinear`'s.
2. `CReal.bounded_on_id_zero_one : BoundedOn (fun r => r) zero one 0` —
   bridges `one` to `mag_bound 0` via `rat_unit_eq_one`
   (`Eq Rat (natDivSucc 1 0) Rat.one`, lifted across `ofRat`), then applies
   `bounded_on_id_unit` directly rather than re-deriving its magnitude
   argument (~35 lines, shorter than the ~60-line route the module doc had
   sketched — see "what I found wrong" below).
3. `CReal.evtLinear_uniformly_continuous : ∀ v, UniformlyContinuousOn
   (evtLinear v) zero one` — `uniformly_continuous_mul` at `F := id`,
   `G := fun _ => v`, both `BoundedOn` arguments discharged by (1) and (2).
   Pure assembly, no new algebra.
4. Module doc in `creal/extreme_value.rs` updated: the "LABELED GAP" section
   is now "CLOSED", and the `evtLinear` field doc comment in `creal.rs` no
   longer says "asserted, not proved".

**What I found wrong in the module doc (now corrected):** it predicted the
`[0,1]` `BoundedOn` case would need `max_le` on `abs`'s two branches plus
`add_le_add` against `le_refl (neg z)`, ~60 lines, built from scratch. The
much cheaper route — transport `hzb : le z one` to `le z (mag_bound 0)` via
the `rat_unit_eq_one` bridge, then apply `bounded_on_id_unit` DIRECTLY at
the transported hypothesis — was available and ~35 lines. Worth knowing for
the next lane that estimates a route by "build from primitives" without
checking whether an existing sibling theorem can just be reused.

**Not attempted / out of scope:** no change to `evt_attained_max_decides_sign`
itself (it never needed continuity as a hypothesis — the gap was purely the
bridge sentence connecting `evtLinear` to classical EVT's hypothesis class).

**Your lane's block (`landed`, drat-evidence-route, 2026-08-28).**

**The question.** Why did the evidence/certificate path call `check_drat` — the
forward reference checker, superlinear in proof length — when
`check_drat_backward` and `elaborate_drat_to_lrat_backward` (ADR-0382, ~66x)
had existed since 2026-08-12? Was there a deliberate reason?

**The answer: no. It is precedence, not a decision.** ADR-0382 was written to be
additive ("`check_drat` must not change, because it is the reference; the new
checker must be additive") and its item 9 explicitly deferred re-basing the LRAT
elaborator as "an obvious follow-on ... deliberately not in this slice". The
follow-on was never taken. `git log -L` dates the accepting call sites in
`evidence.rs` and `proof.rs` to **2026-06-13**, two months before the fast engine
existed. No ADR, comment or test pins them. The backward engine is meanwhile used
throughout the campaign tooling, `cube.rs`, `weighted.rs` and half a dozen
examples — everywhere except the certificate route.

**Why the naive fix was still wrong.** Swapping in `check_drat_backward` at the
accepting sites is exactly what ADR-0382 refused, and for a good reason: it moves
the trusted base from a few dozen readable lines to ~2,700 lines of watched
literals and clause arenas. Speed bought with assurance is not a trade this
repository makes.

**What landed instead (ADR-0613): the fast engine became a producer.**
`certify_unsat_via_lrat` runs `elaborate_drat_to_lrat_backward` as an
**untrusted** emitter of antecedent hints, then has `check_lrat` — small,
search-free, linear — verify those hints against the formula directly. A
`Certified` is discharged by `check_lrat` alone, so a bug anywhere in the
backward engine yields a decline, never a wrong `unsat`. The trusted base does
not grow; it **shrinks**, from a checker that searches for a refutation to one
that is handed it. `check_drat_backward` appears only in *rejecting* position
(the DRAT conjunct in `UnsatProof::recheck`), where it can reject and never
accept. The forward reference is untouched and remains the accepting authority
whenever the LRAT route declines (a RAT lemma, or a checking budget too small for
a stage that cannot be interrupted).

**Measured, `smtcomp_cli --evidence --progress`, release, contended host:**

Detail moved to [`../notes/187-drat-evidence-route.md`](docs/plan/notes/187-drat-evidence-route.md).

**Your lane's block (`DONE`, nat-cascade, 2026-08-28).** All six targeted
facts landed, all kernel-checked and axiom-free (`nat` trusted surface = 0
throughout). `nat_prelude::` went 95 -> 96 passed, 0 failed.

Two of the six turned out to be thin corollaries once mirrored against the
just-landed prerequisites, exactly as the brief predicted: `choose_symm_add`
(one call to `choose_symm_of_eq_add` with `n := a+b` and `refl` for the
hypothesis) and `coprime_of_dvd` (two-step composition of
`coprime_of_dvd_right` then `coprime_of_dvd_left`, no new algebra). The other
four needed real construction:
- `choose_le_add` — induction on `b`, chaining `choose_le_succ` through
  `le_trans` (both cases defeq via `add`'s definitional zero/succ equations).
- `coprime_self_add_right` — `coprime_add_self_right` transported along
  `add_comm` to swap which side of the sum carries `m`.
- `coprime_symmetric` — **no `gcd_comm` lemma existed in the prelude** (the
  brief's "check whether a `gcd_comm` already closes this" came back
  negative); built directly via mutual `gcd_dvd_left`/`gcd_dvd_right` +
  `dvd_gcd` + `dvd_antisymm`.
- `coprime_or_dvd_of_prime` — decided constructively via a local `Bool.rec`
  case split on `beq (gcd p i) one` (mirrored from `totient.rs`'s private
  `bool_true_or_false` helper, duplicated since it is module-private) plus
  `prime_dvd_iff_not_coprime`'s reverse direction. **Not Bezout**, matching
  the brief's warning about the earlier coprime lane.

Kernel rejected nothing on the first accepted attempt for any of the six —
every proof term type-checked once written, so no bisection was needed.

Newly unblocked but out of scope for this lane: `F:ml430-nat-choose-le-choose-907b5042`
(needs `choose_le_add`, now available) and `F:ml430-nat-coprime-of-lt-prime-1978a919`
(needs `coprime_or_dvd_of_prime`, now available).

**Your lane's block (`DONE`, nat-parity, 2026-08-28).** Landed `Nat.Even n :=
Exists (fun k => Eq n (add k k))` and `Nat.Odd n := Exists (fun k => Eq n
(succ (add k k)))` — the `k+k`/`succ(k+k)` form (not `2*k`/`2*k+1`), chosen
because `Nat.even_or_odd` (`powsq.rs`) already produces exactly that shape as
its own branch equations, so `even_or_odd_exists` hands them straight to
`Exists.intro` at witness `div n 2` with no conversion. All three requested
items (1–3) landed with real kernel-checked proofs, plus all of the "bonus"
item 4: `even_not_odd`, `odd_not_even` (via a new
`add_self_ne_succ_add_self : ∀ k j, Not (Eq (add k k) (succ (add j j)))`,
proved by induction on `k` with an inner case split on `j`), and
`even_iff_odd_succ` (direct `congrArg succ`/`succ_injective`, no induction
needed). All seven declarations rest on zero axioms (kernel-verified, not
asserted). New module: `crates/axeyum-lean-kernel/src/nat_prelude/parity.rs`.

`powsq.rs`'s inline even/odd split (`declare_even_or_odd`, the
`Or (Eq n (add half half)) (Eq n (succ (add half half)))` disjunction) was
**not** re-derived — `even_or_odd_exists` calls the existing theorem
`Nat.even_or_odd` as a lemma and repackages its two branches via
`Exists.intro`, with zero new case-analysis machinery. Nothing else this
brief expected to find already-existing (`Nat.Even`/`Nat.Odd` under any
spelling) was present — the grep-with-positive-control the brief specified
came back empty both times, and it stayed empty.

`nat_prelude::` sweep: 95 passed before this lane, 97 passed after (95 + the
previously-failing coverage-inventory assertion, now fixed, + one new
concrete-witness cross-check test). 0 failed throughout. No fact-ledger entry
was created — these are infrastructure declarations with no formal-statement
consumer yet; a downstream lane building `Coprime 2 n ↔ Odd n` or similar
should register the fact then, not here.

Not attempted (explicitly out of scope per the brief): `Coprime 2 n ↔ Odd n`
and any other downstream cascade.

**Your lane's block (`DONE`, int-modeq, 2026-08-28).** Closed all seven
backlog facts (`docs/plan/status/int-modeq-kernel.md` had flagged six of
these — `modeq-add-left`, `modeq-add-left-cancel`, `modeq-dvd-iff`,
`modeq-neg`, `modeq-of-dvd`, `modeq-of-mul-left` — as "not attempted…a
well-scoped next task"; the seventh, `neg-modeq-neg`, was the `Iff` around
`modeq-neg`).

**The hypothesis-mismatch finding was correct.** `declare_modeq_add_left`/
`declare_modeq_add_right` (`int_prelude/modeq.rs`) carried a `0 < n`
hypothesis Mathlib's `Int.ModEq.add_left`/`add_right` do not have. Verified
by reading the declared TYPE (`d.ilt(zero, n)` appears in `pos_ty`, which is
threaded into `stmt` via `d.arrow(pos_ty, inner_arrow)` — not just a local
proof-term detail) and by instantiating at `n = 0` and `n = -3`: the Mathlib
statement holds at both, unconditionally.

**Root cause, and why it generalizes past these two facts.** Re-reading
`declare_modeq_iff_dvd`'s `mp` half (`ModEq n a b → dvd n (b-a)`) shows
`h_pos`/`n_ne_zero` are used ONLY by `mpr` (which needs
`ediv_emod_unique`'s `0<=r<n` uniqueness bound, itself proved positive-only).
`mp` never touches either — it was scoped under `0 < n` only because it was
declared alongside `mpr` inside one `Iff`, not because it needs it. Extracted
as `modeq_to_dvd`, unconditional in `n`.

The converse (`dvd n (b-a) → ModEq n a b`) is ALSO unconditional, but via a
DIFFERENT route than `mpr`'s: a witness `c` with `b-a=n*c` gives `b=n*c+a`
directly (`cancel_neg_add`), and `Int.modEq_add_mul_left : ModEq n (n*q+a) a`
— already unconditional, built by `int-modeq-kernel` — closes it with no
bound at all. Extracted as `dvd_to_modeq`. So BOTH halves of the bridge are
unconditional; `0 < n` on the old `Iff` declaration was solely a proof-route
artifact of routing the converse through `ediv_emod_unique` instead of
`modEq_add_mul_left`.

Detail moved to [`../notes/190-int-modeq.md`](docs/plan/notes/190-int-modeq.md).

**Your lane's block (`DONE`, parity-coprime, 2026-08-28).** All six targeted
facts landed, all kernel-checked and axiom-free (`nat` trusted surface = 0
throughout). `nat_prelude::` went 96 -> 98 passed, 0 failed.

Two facts were cheap: `F:ml430-nat-choose-le-choose-907b5042` needed one new
declaration (`choose_le_choose`, monotone-in-the-row-index, via `choose_le_add`
transported along an additive witness extracted from `Le a b` by
`sub_add_cancel`). `F:ml430-nat-coprime-of-lt-prime-1978a919` needed no new
Rust at all — `declare_coprime_of_lt_prime` (`nat_prelude/primes.rs`) had
already been admitted to the kernel in an earlier commit (`de2e39eee`), via a
direct route that does not actually go through `coprime_or_dvd_of_prime`
despite the fact's recorded `depends_on` edge naming it (that edge predates
the direct proof and was never revisited). Found already-proved, status
flipped, no re-derivation.

The substantive piece, `F:ml430-nat-coprime-two-left-1b47e7c4` (`Coprime 2 n
↔ Odd n`), needed real construction: `2` is prime (a private `prime_two`
helper rebuilding `prime_condition(2)`), `coprime_or_dvd_of_prime` splits
`gcd 2 n = 1 ∨ dvd 2 n`, `prime_dvd_iff_not_coprime` relates `dvd 2 n` to
`Not (gcd 2 n = 1)`, and a private bridge (`even_of_dvd_two`/
`dvd_two_of_even`, via a rebuilt `2*k = k+k` identity) connects `dvd 2 n` and
`Even n` so `even_or_odd_exists`/`even_not_odd` can rule out the even case in
each `Iff` direction. `coprime_two_right`, `coprime_odd_of_left`,
`coprime_odd_of_right` were thin corollaries once `coprime_two_left` existed,
exactly as the brief predicted.

**Did NOT need `add_self_ne_succ_add_self`** (the brief flagged it as a
likely dependency) — the whole construction routes through `dvd`/`gcd`
machinery instead of directly comparing two existential witnesses, so that
theorem never came up.

Detail moved to [`../notes/191-parity-coprime.md`](docs/plan/notes/191-parity-coprime.md).

**Your lane's block (`WIP`, supon-r6b, 2026-08-28).** What landed, what did not,
and what the next lane needs to know. State a negative as precisely as a
positive — a sized negative is a complete deliverable here.

**Your lane's block (`needs-decision`, nat-numeral-accel, 2026-08-28).** The
diagnosis held and is now measured rather than read; the fix works and is sound;
**and the benefit is not where it was expected, while the cost is somewhere
nobody looked.** All three parts matter and only the set of them is honest.

**The mechanism (confirmed, mine).** `NatOps::num` built `succ^n Nat.zero`.
`Kernel::reduce_nat_binop` fires only when both arguments whnf to `Lit::Nat`,
and `Nat.zero` is a constructor with no definition, so a unary tower never does
— ~2,280 numeral call sites across `nat`/`int`/`rat`/`creal`/`complex` were all
on the slow side of a fast path built, tested by four suites, and trusted since
the Lean import work. `examples/nat_numeral_whnf_probe` prices it: `Nat.mul 125
105` 52,399 µs → 10 µs; `Nat.gcd 512 1875` **25.6 s → 16 µs** (1.6 million×);
`Nat.div 13125 25` **stack-overflows** unary, at exactly the magnitude
`Rat.normalize` forms.

**The fix (landed on this branch, ADR-0613).** `num` emits `Lit::Nat(n)`;
`num_unary` keeps the constructor spine. All seven preludes still build, so
every proof term written against the unary form re-passes
`Kernel::add_declaration` — **no proof edited, blast radius zero on proofs**.
Guard: `tests/nat_prelude_numerals_are_literals.rs`, five assertions, each
mutation-verified. Reverting `num` to unary kills exactly the two shape tests
and leaves both defeq tests green, which is the point.

**The benefit is ~zero on today's tree.** Interleaved A/B, same binary from the
two `num` bodies, `AXEYUM_PRELUDE_CACHE=0`: `creal` **14.91 s → 14.23 s**
(4.6%, and a second round under load 6.2 put the *unary* side at 23.4 s — noise
larger than the effect); `nat` 193.5 → 191.2 ms; `rat` 762.6 → 784.4 ms.
**Treat `creal_prelude_builds` as unchanged.** The committed preludes do not
spend meaningful time reducing closed `Nat` at large magnitudes; the 587 s →
113.5 s incident was one declaration forming a 13,125-magnitude `Nat`. What the
change buys is that the shape stops being a landmine, not that today is faster.

Do not quote the brief's 94.85 s `creal_prelude_builds` figure. Measured here on
`main` at `f3ecf4004`, release, cache off: **15.54 s / 15.35 s** via
`prelude_build_timing` — a different harness from the test, but nothing near 94 s
either way.

Detail moved to [`../notes/193-nat-numeral-accel.md`](docs/plan/notes/193-nat-numeral-accel.md).

**Your lane's block (`DONE`, main-red-tests, 2026-08-28).** Both failures were
pre-existing on `main`, both reproduced, both diagnosed to a named cause, both
fixed. `cargo test -p axeyum-solver --lib --features full` is **1438 passed, 0
failed** with `RUST_MIN_STACK` unset, and `-p axeyum-bench --test
qfbv_proof_export` is 2/2.

## 1. `monomial_bound` (and three more modules) — the `creal` prelude outgrew the default stack

**It reproduces in `--release`**, so the brief's discriminator fires — but the
requirement is **finite and bounded in both profiles**, which the "fails in
release ⇒ runaway recursion" heuristic does not distinguish. Measured two
independent ways:

| what | debug | release |
| --- | --- | --- |
| `--measure --prelude creal` (smallest power of two) | 16,777,216 | 8,388,608 |
| pinned in `artifacts/kernel-stack-envelope.tsv` (2026-08-26) | 2,097,152 | 131,072 |
| fine bisection of the release test binary | — | aborts at 4,456,448, completes at 4,587,520 |

So the cause is not a false assertion and not a non-terminating term: the
`CReal` development's stack requirement grew **8x in debug and 64x in release
in two days**, past the 2 MiB a `#[test]` thread gets by default.
`scripts/check-kernel-stack-envelope.sh --check --prelude creal` — the gate that
exists precisely to convert this symptom into an explained failure — is **red on
`main`**, and nobody ran it.

The blast radius is wider than the two tests the reporting lane named, because a
stack overflow aborts the whole process and kills the rest of the run. Every
test that builds the constructed reals was affected:
`reconstruct::arithmetic::{monomial_bound, zero_product, product_positivstellensatz,
signature::signature_tests}` and `reconstruct::tests`. Only the first to run
reported.

Fixed at the one place they all funnel through:
`LraReconstructCtx::try_new_over_constructed_reals_reporting` now builds on a
256 MiB worker (16x the measured debug requirement, the workspace's
`DEEP_STACK_BYTES` figure), which also covers the front-door
`try_new_over_constructed_reals` path where an overflow would have aborted a
consumer's process. The one direct `build_creal_prelude` outside that
constructor, in `signature_tests::creal_signature`, uses the same helper.

Detail moved to [`../notes/194-main-red-tests.md`](docs/plan/notes/194-main-red-tests.md).

**Your lane's block (`DONE`, fp16-evidence, 2026-08-28).** `F:fp16-add-monotone-rne`
is now `epistemic_status: proved`. Rebuilt `smtcomp_cli --release` from
scratch in this worktree and ran it end to end against the fact's own pinned
negation file TWICE: both `unsat`/`certified=1`/`recheck=ok`/`arena=ok`.
Wall clock 339.01s (load ~2.8/16) and 353s (load ~20.7/16) -- **not** the
~125s ADR-0613's prose calls "end to end": that figure is a sub-stage timer
captured before `UnsatProof::recheck()` and the `arena` fresh-parse check
run (both inside `evidence_report_line`, after the timer stops). Wrote one
`unsat-certificate` evidence row whose `checker_command` greps the real
process output for three independently-tested, discriminating substrings
(`^unsat$`, `certified=1 `, `recheck=ok`) via `test`-chained `&&`, verified
against both a captured real positive transcript and two synthetic
negative-control transcripts before being written. `checker_seconds: 400`
(budget 800s under the replay gate's 2x rule) to absorb contention.
`validate-facts.py` passes: 0 errors, `smt-clausal=10` (was 9), `open=155`
(was 156). No exhaustive enumeration exists or was attempted at this width
(2^48 triples); this fact rests on the symbolic CNF/DRAT/LRAT route alone,
unlike its fp8 sibling which has two independent routes.

**Your lane's block (`DONE for the three landed; one fact deliberately
deferred with a sized reason`, int-gcd, 2026-08-28).** Closed
`F:ml430-int-ne-zero-of-gcd-f71f00df`,
`F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82`, and
`F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222`, each via a
genuine new kernel declaration in `int_prelude/gcd.rs`
(`declare_ne_zero_of_gcd`, `declare_gcd_eq_one_of_gcd_mul_right_eq_one`).
Left `F:ml430-int-gcd-div-5e01872f`, `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`,
and `F:ml430-int-gcd-greatest-5b31c5fe` untouched (not attempted — see
below); did not close `F:ml430-int-gcd-eq-gcd-ab-63005aef` (the brief's
"interesting one" — my characterization of it was correct, see below).

**The brief's characterization of `Int.gcd_eq_gcd_ab` was RIGHT, and the
closing work is LARGER than "small but real".** The kernel's existing
`Int.gcd_eq_gcd_ab` proves `∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v` —
confirmed by reading `declare_gcd_eq_gcd_ab` in `gcd.rs` line-by-line: the
`stmt` it builds is an `Exists`/`Exists` nest (`exists_name` applied twice),
never a named witness. Mathlib's `Int.gcd_eq_gcd_ab` is
`∀ x y, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y` — computable projections,
not an existential. These are different propositions.

Detail moved to [`../notes/196-int-gcd.md`](docs/plan/notes/196-int-gcd.md).

**Your lane's block (`DONE`, nat-helper-dedup, 2026-08-28).** Promoted the
three genuine duplicate groups the brief named, all confirmed byte-for-byte
identical before consolidation:

- `two_divisor_dichotomy` (`d ∣ 2 → d = 1 ∨ d = 2`) — three copies:
  `irrational.rs`'s `two_divisor_dichotomy`, `perfect.rs`'s `divisors_of_two`,
  and a third inlined directly inside `primes.rs`'s `Nat.prime_two`
  construction (not its own `fn`, but the identical term-building sequence).
  Promoted to `nat_prelude/ops.rs` as `pub(super) fn two_divisor_dichotomy`,
  self-contained (uses an inline `or_rec` application rather than depending
  on `or_elim`/`or_cases`, since those remain private per-file combinators
  used extensively elsewhere in `irrational.rs` and `primes.rs`). 4 call
  sites re-pointed (1 in `irrational.rs`, 2 in `perfect.rs`, 1 inlined
  construction in `primes.rs`'s `prime_two` replaced with a direct call).
- `two_mul_eq_add_self` (`Eq (mul two k) (add k k)`) — two copies:
  `powsq.rs`'s `two_mul_eq_add_self` and `primes.rs`'s
  `two_mul_eq_add_local`. Promoted to `ops.rs` under the more descriptive
  original name. 4 call sites re-pointed (2 in `powsq.rs`, 2 in `primes.rs`).
- `bool_true_or_false` (`Or (beq b true) (beq b false)`, `Bool.rec`) — the
  brief named two copies (`totient.rs`, `primes.rs`); a third turned up while
  re-pointing call sites: `perfect.rs` had its own copy too, used at **5**
  internal call sites, byte-identical and even self-documented as "local
  copy of `totient.rs`'s `bool_true_or_false`" — so the duplication was
  already known and recorded, just never acted on. All three promoted to
  `ops.rs`. 7 call sites re-pointed total (1 `totient.rs`, 1 `primes.rs`, 5
  `perfect.rs`).

Placed in `nat_prelude/ops.rs` rather than `helpers.rs`: the brief named
`ops.rs` as the shared-machinery location, `ops.rs` is in this lane's scope
and `helpers.rs` is not, and every one of the five touched files already
`use super::ops::{NatDev, NatOps}`, so promoting into that same module means
callers just widen an existing import rather than adding a new one.

Detail moved to [`../notes/197-nat-helper-dedup.md`](docs/plan/notes/197-nat-helper-dedup.md).

**Your lane's block (`landed`, modeq-producer, 2026-08-28).** The task was to
move the *multi-target operation* counter, not the theorem count.

**Measured, `gen-production-provenance-ledger.py`:**
`via_multi_target` **19 -> 30**, `multi_target_operations` **4 -> 5**,
`operations` 28 -> 29. Eleven facts that were `open` at lane start are now
`proved`, every one of them through an operation that names more than one
target.

**Holdout isolation, before and after, unchanged and PASS:**
`held_out=37|settled=0|references=0`. All eleven open `nat.modeq` targets are
in the **development** partition and the eleventh open sibling this lane also
closed is **train**; nothing held-out was referenced, so no target was dropped
on partition grounds.

**What was actually built.**

- `producers::conclusion_directed_application` (new). The existing
  `bounded_application` grows a forward product closure and its 128-term
  budget is exhausted at application depth 4; **eight of the ten `Nat.ModEq`
  targets need a five-argument application and all eight declined with
  `NoTypedApplication`.** The new producer peels the goal's binders, peels each
  candidate into holes, first-order-matches the candidate's conclusion against
  the goal terminal, and discharges the remaining holes from the goal's own
  binders with bounded backtracking. 10 of 10 accepted, `axioms=0`,
  `target_dependency=false`.
- `scripts/lean/autogenesis_nat_modeq_congruence_contract_v1.lean` — ten
  axiom-free Lean candidates. Every public Lean 4.30 `Nat` remainder lemma
  carries `propext` (measured: `mod_zero`, `mod_eq_of_lt`, `add_mod`,
  `mod_mod_of_dvd`, `mod_self`), so the `Nat.mod` recurrence is rebuilt over
  `Nat.modCore`/`Nat.modCore.go` and every law derived from it by structural
  fuel induction.
- `Int.modEq_of_mul_right` in `int_prelude/modeq_family.rs` — the one still-open
  **train** member of `integer-modular-equivalence`, a twenty-line mirror of
  `declare_modeq_of_mul_left` at `Int.dvd_mul_right`.

**Two findings worth carrying.**

Detail moved to [`../notes/198-modeq-producer.md`](docs/plan/notes/198-modeq-producer.md).

**Your lane's block (`landed`, nat-log, 2026-08-28).**

Twelve `nat.log` and eight `nat.clog` ledger facts were open behind a gap that
was not "unproved" but **unstatable**: neither `Nat.log` nor `Nat.clog` existed
in this kernel. `Nat.log` now does, with six theorems, all admitted through
`Kernel::add_declaration` with an empty `axiom_footprint`.

**The obstacle, and how it was cleared.** Mathlib v4.30 is
`Nat.log b n = if 1 < b ∧ b ≤ n then log b (n / b) + 1 else 0` — the recursive
call is at `n / b`, which is **not a constructor predecessor**, so this is not
structural recursion. Mathlib uses well-founded recursion; the Lean equation
compiler's route to that carries `Quot.sound`/`propext`, which would be fatal
to this project's headline metric (a sibling lane measured exactly that on
`Nat.gcd.eq_def` the same day).

The prelude already had the answer and it needed no new machinery:
`declare_executable_division` defines `Nat.div`/`Nat.mod` by structural
recursion carrying a rolling state. `Nat.log` uses the same device one level
up — **structural recursion on a FUEL argument**, instantiated at `n` itself,
which always suffices because the guard forces `2 ≤ b ≤ n` and therefore
`n / b ≤ n / 2 < n`:

```text
Nat.logAux b 0        n ≡ 0
Nat.logAux b (succ f) n ≡ if b ≤ n then (if 2 ≤ b then succ (logAux b f (n / b)) else 0) else 0
Nat.log b n           := Nat.logAux b n n
```

Both equations are **definitional** (β/δ/ι), so there are no equation lemmas
and nothing appeals to an axiom. **No `WellFounded`, no `Quot.sound`, no
`propext`, no new kernel machinery of any kind.**

**Two design points worth carrying forward.**

- *The guard's nesting order is load-bearing, and it is `b ≤ n` outermost.* The
  two cuts commute semantically but not for proof cost: only the outermost cut
  collapses the whole term with one rewrite. With `b ≤ n` outermost, `log_of_lt`
  is a single `Eq.rec`; nested, it would also need `bool_select c 0 0 = 0`, a
  case analysis on the *other* cut. Nothing is given up, because `ble zero y`
  reduces to `Bool.true` unconditionally, so the outer cut never blocks the
  base-`0`/base-`1` equations.
- *An exhausted fuel returns `0`, which is exactly what a wrong logarithm looks
  like.* So the computation test is the fuel-sufficiency check, not a nicety.

Detail moved to [`../notes/199-nat-log.md`](docs/plan/notes/199-nat-log.md).

**Your lane's block (`DONE`, nat-factorial, 2026-08-28).** Landed four of the
six assigned facts: `Nat.factorial_dvd_factorial`, `Nat.factorial_le`,
`Nat.factorial_lt_of_lt`, `Nat.factorial_ne_zero`, all `kernel-lean`,
axiom-free (`nat` trusted surface still 0). `factorial_le`/`factorial_lt_of_lt`/
`factorial_ne_zero` had to move OUT of `declare_divisibility` into a new
`declare_factorial_order` (`divisibility.rs`) called after `declare_euclid` in
`build_nat_prelude`'s dispatcher — all three need `one_le_factorial`, which
`declare_euclid` (`primes.rs`) declares, and `declare_euclid` runs after
`declare_divisibility`. Same shape as the documented `declare_dvd_antisymm`
precedent in `lcm.rs`; `UnknownConst { name: NameId(306) }` was the tell, not
`TypeMismatch`.

The remaining two — `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` and
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` — are left **open**.
`Nat.ascFactorial`/`Nat.descFactorial` do not exist in this kernel: no field on
`NatPrelude`, and `asc_factorial`/`desc_factorial`/`ascFactorial`/
`descFactorial` all grep to zero hits anywhere in
`crates/axeyum-lean-kernel/src/`. The prelude struct field list is the
authoritative registry here (every field is declared exactly once, at
construction), so this is a confirmed absence, not an unfound search — matches
the brief's expectation. Building the two ascending/descending factorial
definitions plus their base-case facts (`F-ml430-nat-ascfactorial-zero-…`,
`F-ml430-nat-descfactorial-zero-…`, etc. — eight open facts already sit in the
ledger for this family) is out of scope for an import-backlog lane and is the
next lane's task if picked up.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 98 passed, 0 failed
(347 → 351 theorems; `the_build_is_deterministic`'s pin recounted by reading
its own panic message, not incremented by hand).
`cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.

**Your lane's block (`WIP`, nat-prime, 2026-08-28).** Landed four of the
seven open `Nat.Prime` facts: `Nat.prime_odd_of_ne_two`, `Nat.prime_even_iff`,
`Nat.prime_not_dvd_mul`, `Nat.prime_dvd_of_dvd_pow`, all in
`nat_prelude/primes.rs`. Remaining open: `prime_dvd_mul_of_dvd_ne` (needs a
`coprime_primes` argument -- two distinct primes are coprime -- not yet
built anywhere in the tree; its own fact, `F:ml430-nat-coprime-primes-
5769049f`, is itself open) and `prime_five_le_of_ne_two_of_ne_three` (needs
a bounded case split ruling out `p ∈ {2,3,4}`, which in turn needs small
numeral facts this prelude does not yet carry -- `2 ≠ 4`, `dvd 2 4`, and a
"primality of 4 is false" argument -- none reused from elsewhere). Final
`nat_prelude::` sweep: 98 passed, 0 failed (up from 97 at lane start).

**Your lane's block (`WIP`, frontier-split, 2026-08-28).** Landed the kernel
declaration coverage check `docs/research/11-design-review/
2026-08-28-is-the-open-frontier-stale.md`'s addendum asked for:
`fact-frontier.py` used to print `proof route only -- needs a kernel proof`
for both an unproved-but-statable fact and a fact naming a function that
does not exist under any name in this kernel. Now the second state is
reported as `BLOCKED -- statement names undeclared kernel definition(s):
<names> (build these first; this is not a proof task)`, with the missing
name(s) printed.

**The check is derived from the kernel, never a hand list**, per the
brief's non-negotiable: it reads `kernel_declaration_projection`'s
unfiltered TSV emit (the prebuilt `--release` binary at
`target/release/examples/kernel_declaration_projection`, run DIRECTLY --
no `cargo run`, no cargo lock, so `just next` never triggers a build) plus
every SETTLED fact's own `formal.statement` in this ledger, as a
corroborating signal. A candidate identifier is reported missing only when
its namespace is one this kernel implements, it is not itself a declared
name, AND no proved fact's statement has ever used it either.

**The corroboration clause was not in the brief and turned out to be
load-bearing.** A naive name-check (namespace known + not declared) flags
`Nat.Prime`/`Nat.Coprime` on every `nat.prime`/`nat.coprime` fact, because
primality and coprimality are built INLINE in this kernel (no `Nat.Prime`
declaration exists) rather than as named declarations -- CLAUDE.md's
"hiding place 2". Without corroboration this check would have manufactured
23 new false positives (7 `nat.prime` + 8 `nat.coprime`... measured: 15
open facts across those two families) on top of the real 30, which is
exactly the "checker that cannot fail" defect this repository keeps
finding, just inverted (crying wolf instead of staying silent). Read from
the ledger itself: a name used in an already-PROVED fact's statement is
corroborated, so it is never flagged even though it carries no kernel
declaration.

Detail moved to [`../notes/202-frontier-split.md`](docs/plan/notes/202-frontier-split.md).

**Your lane's block (`landed`, nat-sqrt, 2026-08-28).**

`scripts/fact-frontier.py` reported 14 open facts as `BLOCKED — statement
names undeclared kernel definition(s): Nat.sqrt`, the largest single blocker
on the frontier. `Nat.sqrt` now exists, with two boundary theorems
(`sqrt_zero`, `sqrt_one`), both admitted through `Kernel::add_declaration`
with an empty `axiom_footprint`. Two new facts (`F:nat-sqrt-zero`,
`F:nat-sqrt-one`) are `proved`; the 14 `F:ml430-nat-sqrt-*` mirror facts stay
`open` — see "not attempted" below.

**The obstacle, and how it was cleared.** Mathlib v4.30 `Nat.sqrt` is a
Newton's-method iteration under well-founded recursion (`iter (n guess) := let
next := (guess + n/guess)/2; if next < guess then iter n next else guess`).
That is not structural, and the Lean equation compiler's route to
well-founded recursion carries `Quot.sound`/`propext` — fatal to this
project's axiom-freedom metric, and exactly the trap `Nat.log` (landed an
hour earlier, `docs/plan/status/199-nat-log.md`) sidestepped the same way.

This file follows `log.rs`'s established pattern — **structural recursion on
a fuel argument** — but the recursion shape itself did not transfer verbatim,
because `Nat.sqrt` has one argument to `Nat.log`'s two and its "state" is an
accumulator that only ever grows, not a shrinking second argument:

```text
Nat.sqrtAux n 0        ≡ 0
Nat.sqrtAux n (succ f) ≡ let c := Nat.sqrtAux n f
                         in if (succ c) * (succ c) <= n then succ c else c
Nat.sqrt n             := Nat.sqrtAux n n
```

The target `n` is a captured free variable, not threaded through `Nat.rec`'s
motive at all — the motive here is the plain `fun _ => Nat` (an accumulator
fold), simpler than `logAux`'s `fun _ => Nat -> Nat` (which needed a
function there because `log`'s recursive argument, `n / b`, genuinely
changes per fuel level; `sqrt`'s target never does). `n` always suffices as
fuel: the accumulator starts at `0` and grows by at most `1` per step, and
the greatest `m` with `m * m <= n` is itself `<= n`.

Both equations are **definitional** (β/δ/ι) — no equation lemmas, no
`WellFounded`, no `Quot.sound`, no `propext`, no new kernel machinery.

Detail moved to [`../notes/203-nat-sqrt.md`](docs/plan/notes/203-nat-sqrt.md).

**Your lane's block (`landed`, nat-clog, 2026-08-28).**

Four boundary facts (`clog_zero_left`, `clog_zero_right`, `clog_one_left`,
`clog_one_right`) were `BLOCKED` on an undeclared kernel definition,
`Nat.clog`. It now exists, with two definitions and four theorems, all
admitted through `Kernel::add_declaration` with an empty `axiom_footprint`.

**The 199-nat-log lane's sketch was RIGHT, and the fuel device transferred
verbatim.** Mathlib v4.30's `Nat.clog b n = if 1 < b ∧ 1 < n then clog b ((n +
b - 1) / b) + 1 else 0` has the same non-structural shape as `Nat.log` — the
recursive call is at `(n + b - 1) / b`, not a constructor predecessor — so it
gets the same treatment: structural recursion on a FUEL argument, instantiated
at `n` itself.

```text
Nat.clogAux b 0        n ≡ 0
Nat.clogAux b (succ f) n ≡ if 2 ≤ b then (if 2 ≤ n then succ (clogAux b f ((n + b - 1) / b)) else 0) else 0
Nat.clog b n           := Nat.clogAux b n n
```

Both equations are definitional (β/δ/ι); nothing here appeals to an axiom.

**One design point differs from `log.rs`, and it is the guard nesting order —
the OPPOSITE of `log`'s.** `log`'s guard mixed a `b`-only cut (`2 ≤ b`) with a
cut relating `b` and `n` (`b ≤ n`), and needed the mixed cut outermost for
`log_of_lt`. `clog`'s guard (`2 ≤ b ∧ 2 ≤ n`) has **two single-variable cuts**,
and the four theorems this lane proves split cleanly: `clog_zero_left`/
`clog_one_left` fix `b` and vary `n`, so they need the `b`-only cut (`2 ≤ b`)
outermost to collapse in one rewrite regardless of `n`; `clog_zero_right`
never reaches the guard at all (fuel `0`, pure `refl`); `clog_one_right` fixes
`n = 1`, so its `n`-only cut (`2 ≤ 1`) is a closed `false` no matter which
branch of a 3-way case split on `b` it is reached from. `2 ≤ b` outermost
serves every theorem here, so — unlike `log`, where the ordering was a real
tradeoff against `log_of_lt` — there was no tension to resolve.

Detail moved to [`../notes/204-nat-clog.md`](docs/plan/notes/204-nat-clog.md).

**Your lane's block (`landed`, producer-widen, 2026-08-28).** Task: widen
`producers::conclusion_directed_application` (lane 198, which closed ten open
`nat.modeq` facts) to a **second** family of currently-open facts.

**Outcome: no operation registered, so `facts_via_multi_target` is unchanged.**
(`operations=29`, `multi_target_operations=5`, and a read-only recomputation
over `operations.json` x fact status gives `facts_via_multi_target=31`, one
above the 30 the brief quotes; `gen-production-provenance-ledger.py --check`
was already stale on `main` before this lane started and was **not**
regenerated here, since regenerating would commit another lane's pending
delta.)
The lane found — and this is the deliverable — that the binding constraint is
not the producer's grammar and not family shape. It is that **Mathlib's own
proof is axiom-bearing for 61 of the 63 resolvable open propositions**, so no
transport can close them, and every widening must AUTHOR an axiom-free contract
per family. Three measurements, each re-derivable.

**Holdout isolation, before and after, unchanged and PASS:**
`held_out=37|files_scanned=1101|settled=0|references=0`. The two entirely
held-out families (`natural-logarithm` 21 open, `natural-square-root` 16 open —
37 facts, the whole partition) were excluded by **partition per fact**, never by
count, and no held-out target was measured, exported, or named. **No target was
dropped for any other reason**; nothing outside the exclusion was skipped.

## 1. The producer reaches 0 of 35 open palette facts

Every open, non-held-out fact with a proof-free target capsule in
`/nas3/.../reference-packs/open-fixed-palette-v1` (35), through
`examples/conclusion_directed_transport_probe`:

| outcome | count |
| --- | --- |
| accepted | **0** |
| declined at statement import (`dif_pos` 11, `Quot` 9, `Eq.subst` 3, `Nat.mod_lt` 2, `propext` 1) | **26** |
| imported, then `NoConclusionMatch` | **9** |

Detail moved to [`../notes/205-producer-widen.md`](docs/plan/notes/205-producer-widen.md).

**Your lane's block (`landed`, nat-log-tier, 2026-08-28).**

`log.rs`'s own module doc, written the same day `Nat.log` first landed, named
the next obstacle precisely: `log_le_self`, `log_lt_self`, `log_mono_right`,
`clog_pos`, `log_le_clog` all need `logAux b f n <= f` proved with the VALUE
argument generalized inside the motive of an induction on the FUEL argument
(`fun f => forall n, Le (logAux b f n) f`), because the recursive call inside
`logAux b (succ f) n` is at `logAux b f (n / b)` — a *different* `n` than a
fixed-`n` induction's hypothesis would cover.

**`Nat.logAux_le_fuel` landed on the first kernel attempt**, plus
`Nat.log_le_self` (its `f := n` diagonal specialization, since
`log b n := logAux b n n` definitionally). Both axiom-free, both admitted
through `Kernel::add_declaration`, both covered by
`every_nat_declaration_is_checked_and_axiom_free` (environment-derived, not a
hand list) and by a new concrete-instantiation test at `(b, f, n) = (2, 8, 3)`
/ `(b, n) = (2, 8)` with a swapped-operand negative control.

**The motive generalization was exactly the whole difficulty**, not something
else on top of it — once stated, the two-case step (below) closed without a
second attempt. The technique already existed in this prelude:
`parity.rs`'s `declare_add_self_ne_succ_add_self` quantifies its own inner
variable inside an outer induction's motive the identical way (`d.pi_fv` for
the inner `∀`, built by the SAME closure that also computes the outer
`motive_at`).

**The proof, precisely:**
- *Base* (`f = 0`): `logAux b 0 n` is the constant-zero row, so the goal
  reduces to `Le 0 0`, closed by `Nat.le_refl`.
- *Step* (`f = succ m`, `ih : ∀ n, Le (logAux b m n) m`): reconstruct
  `logAux b (succ m) n`'s normal form exactly as `log_of_lt`'s step case
  already does (`log_aux(d, &p, base, predecessor, quotient)` — the kernel's
  own delta+iota unfold reaches the identical term), then case-split BOTH
  nested `Nat.ble` cuts with a new local helper, `le_of_bool_select`. It
  generalizes `log_of_lt`'s single-branch `bool_transport` technique two
  ways at once: to *both* branches of a cut (that proof only ever needed the
  refuted one), and to an inequality goal in place of an equation. Either
  cut false: the term is `0`, closed by `Nat.zero_le`. Both cuts true: the
  term is `succ (logAux b m (n / b))`, closed by `Nat.le_succ_succ` applied
  to `ih (n / b)`.

Detail moved to [`../notes/206-nat-log-tier.md`](docs/plan/notes/206-nat-log-tier.md).

**Your lane's block (`landed`, nat-bitwise, 2026-08-28).**

The frontier reported `Nat.bit`, `Nat.bitwise`, `Nat.bits`, `Nat.ldiff` as
BLOCKED — undeclared kernel definitions, so the `F:ml430-nat-bitwise-*` /
`F:ml430-nat-land-bit-*` / `F:ml430-nat-lor-bit-*` / `F:ml430-nat-ldiff-bit-*`
mirror facts could not even be *stated*. Per the brief, only `Nat.bit` was
attempted — it is the cheapest of the four and unblocks the most — and
landing it plus real boundary lemmas was the target for a complete success.

**`Nat.bit` landed, and it needed no fuel device at all.** Mathlib defines
`bit b n := cond b (2*n+1) (2*n)` — a plain case split on the `Bool`
argument, no recursive call anywhere. Unlike `Nat.log`/`Nat.sqrt`/`Nat.clog`
(all landed earlier the same day, all non-structural and requiring the fuel
device this prelude uses for `Nat.div`/`Nat.mod`), `Nat.bit` is declared as
an ordinary non-recursive lambda: `bit b n := add (mul 2 n) (cond b 1 0)`.

**The `add`-outermost form (rather than Mathlib's `cond`-outermost one) was
a deliberate choice, not an accident of translation.** Both normalize to the
same value at every literal `b` — `add x zero ≡ x` collapses the false
branch to `2n`, `add x (succ zero) ≡ succ (add x zero) ≡ succ x` collapses
the true branch to `succ (2n) = 2n+1` — but the `add`-outermost form buys
something Mathlib's shape does not: `bit true n` unfolds all the way to
`succ (mul 2 n)` by delta+iota alone, so a lemma about `succ` in general
(`zero_lt_succ`, `le_succ`) applies to it **directly by defeq, with no
case-split combinator**. `log.rs`'s `le_of_bool_select` had to build that
combinator by hand for the analogous situation in `Nat.log`; `bits.rs` never
needed to.

**Four theorems landed, all on the first `Kernel::add_declaration` attempt —
nothing was rejected:**
- `bit_false : ∀ n, bit false n = mul 2 n` — `Eq.refl`.
- `bit_true : ∀ n, bit true n = add (mul 2 n) 1` — `Eq.refl`.
- `bit_true_pos : ∀ n, 0 < bit true n` — `zero_lt_succ (mul 2 n)`, accepted
  by defeq against the unfolded statement.
- `bit_false_le_bit_true : ∀ n, bit false n <= bit true n` — `le_succ
  (mul 2 n)`, accepted by defeq the same way.

Detail moved to [`../notes/207-nat-bitwise.md`](docs/plan/notes/207-nat-bitwise.md).

**Your lane's block (`DONE`, nat-gcd, 2026-08-28).** Closed 9 of the 12 open
`natural-gcd` facts (all `development`, none `held-out` — verified against
`nursery-v1.json` before starting). All 9 proofs go through the
divisibility characterization (`gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd`/
`dvd_antisymm`/`eq_one_of_dvd_one`, plus `dvd_lcm_left`/`dvd_lcm_right`/
`dvd_trans` for the lcm ones) — **none needed to unfold `Nat.gcd`'s
well-founded recursion**, so none hit the `Quot.sound` wall the brief warned
about.

Landed, each independently kernel-verified and axiom-free (`nat` trusted
surface stays 0):

- `Nat.not_coprime_zero_zero : ¬ gcd 0 0 = 1` — `gcd_zero_left` gives
  `gcd 0 0 = 0`; `succ_ne_zero` refutes `0 = 1`.
- `Nat.coprime_one_left_iff : gcd 1 n = 1 ↔ True` and
  `Nat.coprime_one_right_iff : gcd n 1 = 1 ↔ True` — `gcd_dvd_left`/
  `gcd_dvd_right` plus `eq_one_of_dvd_one` give the equation
  unconditionally.
- `Nat.coprime_add_self_left : gcd (m+n) n = 1 ↔ gcd m n = 1` — swap both
  sides of `coprime_add_self_right(n, m)` through `coprime_symmetric`.
- `Nat.coprime_self_add_left : gcd (m+n) m = 1 ↔ gcd n m = 1` —
  `coprime_add_self_left(n, m)` transported along `add_comm`, the same
  congruence-transport shape `coprime_self_add_right` uses.
- `Nat.dvd_lcm_of_dvd_left` / `Nat.dvd_lcm_of_dvd_right` — `dvd_trans`
  through `dvd_lcm_left`/`dvd_lcm_right`.
- `Nat.dvd_of_lcm_left_dvd` / `Nat.dvd_of_lcm_right_dvd` — `dvd_trans`
  through `dvd_lcm_right`/`dvd_lcm_left` composed with the hypothesis.

All 9 declared in `nat_prelude/primes.rs` (kept there rather than in
`gcd.rs`, matching the file's own existing convention: every other
`Coprime`-shaped lemma — `coprime_of_dvd_left/right`, `coprime_symmetric`,
`coprime_add_self_right`, `coprime_self_add_right` — already lives in
`primes.rs`, not `gcd.rs`; `gcd.rs` owns only `Nat.gcd`'s definition and its
raw `gcd_dvd_*`/`dvd_gcd`/`dvd_gcd_iff` characterization). The 4
lcm-transitivity lemmas also went into `primes.rs` rather than `lcm.rs`,
since `lcm.rs` was explicitly out of scope (read-only) for this lane — they
only *consume* `p.lcm`/`p.dvd_lcm_left`/`p.dvd_lcm_right`/`p.dvd_trans`
through the shared `NatPrelude` fields, `lcm.rs` itself is untouched.

`nat_prelude` count: **73 + 369 = 442 before, 73 + 378 = 451 after** (9 new
theorems, 0 new definitions), read off `the_build_is_deterministic`'s own
panic message, not hand-counted.

Detail moved to [`../notes/208-nat-gcd.md`](docs/plan/notes/208-nat-gcd.md).

**Your lane's block (`DONE this pass`, fib-backlog, 2026-08-28).** Closed
three of seven open `natural-fibonacci` facts. Zero of six `integer-fibonacci`
facts are reachable — `Int.fib : ℤ → ℤ` does not exist as a kernel
declaration (confirmed with `shape_search`, fresh build, `declarations=2000`);
every open Int fib fact, including the brief's stated keystone
`F:ml430-int-fib-add-181b6a2c`, quantifies over `Int.fib m`/`Int.fib n` for
genuinely negative `m, n : ℤ`, not `ofNat (Nat.fib n)`. `int_prelude/fibonacci.rs`
only ever builds `ofNat (Nat.fib n)` terms (used by `Int.fib_cassini`); it
never declares an `Int.fib` function. Building one (case-split on sign, with
the standard `fib(-n) = (-1)^(n+1) fib(n)` extension) is a genuine new-carrier
task, not a proof gap — the "unstatable, not unproved" case the brief
carved out. Did not attempt it.

Closed, forming one dependency chain:
- `Nat.fib_add_two_strictmono` — `StrictMono (fun n => fib (n+2))`.
- `Nat.fib_strictmonoOn` — `StrictMonoOn Nat.fib (Set.Ici 2)`, from the above.
- `Nat.fib_lt_fib` — `2 <= m -> (fib m < fib n <-> m < n)`, from the above
  plus the already-proved `Nat.fib_mono`.

Not attempted: `Nat.fastfib_eq` (needs a `Nat.fastFib` fast-doubling
definition that does not exist — same "needs a carrier" shape as the Int
family, smaller); `Nat.le_fib_self` / `Nat.le_fib_add_one` (a second,
independent chain — sized but not started, see below); the
`F:ml430-mutation-*` fib fact (an outcome-blind mutation of `fib_eq_zero`
that is FALSE as stated at `n=1`, so "closing" it means refutation, a
different task shape than proving the other twelve).

`Nat.le_fib_self : 5 <= n -> n <= fib n` is a second two-step-recursion
induction (pair `P(k+5) /\ P(k+6)` by ordinary induction on `k`, mirroring
`fib_add`'s device), sized at roughly the same effort as the strictmono
chain; `Nat.le_fib_add_one` is a two-line composition once it lands (small-`n`
concrete check for `n<5`, `le_fib_self` plus `le_add_right` for `n>=5`). Left
for the next lane rather than rushed.

**Your lane's block (`DONE`, int-bezout-witnesses, 2026-08-28).**
`F:ml430-int-gcd-eq-gcd-ab-63005aef` is **closed**, axiom-free, at Mathlib
v4.30's exact statement `∀ x y : ℤ, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y`.
Six declarations landed in
`crates/axeyum-lean-kernel/src/int_prelude/bezout_witnesses.rs` — three
`Definition`s that return data (`Nat.xgcdAux`, `Nat.gcdA`/`Nat.gcdB`, plus
`Int.gcdA`/`Int.gcdB`) and three `Theorem`s (`Nat.xgcdAux_sound`,
`Nat.gcd_eq_gcd_ab`, `Int.gcd_eq_gcd_ab_witnesses`). Every one measures
`axiom_footprint = 0`.

**The characterization the brief carried was correct.** The pre-existing
`Int.gcd_eq_gcd_ab` is the EXISTENTIAL form
(`∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v`, `int_prelude/gcd.rs:1448`), its
magnitude witnesses come from `Nat.gcd_bezout` — a `Theorem` whose four
naturals sit inside a `Prop` — and its sign handling is a `Prop`-typed
`Or`-elimination. Neither is projectable, so this was a program to write, not
a proof to rearrange. The old name is kept for the existential because
`crt.rs` and `modinv.rs` consume it; the Mathlib-shaped statement is
`Int.gcd_eq_gcd_ab_witnesses`.

**Fuel, and why `m` suffices.** `Nat.xgcdAux` recurses structurally on a fuel
argument (`log.rs`'s device, never `WellFounded`), with a trailing `Bool`
selecting which coefficient to return so ONE recursion carries the pair
without a product type. `Nat.gcdA m n := xgcdAux m m n true`. The invariant
is `m ≤ fuel`, carried as an explicit hypothesis on `Nat.xgcdAux_sound` and
preserved because `succ k ≤ succ f` gives `k ≤ f` while `Nat.mod_lt` gives
`n % succ k < succ k`; at `fuel := m` it discharges to `le_refl`. The bound
constrains the PROOF, not the definition — short of fuel the function still
computes, it just answers for a truncated recursion.

**Three things worth carrying forward.**

Detail moved to [`../notes/210-int-bezout-witnesses.md`](docs/plan/notes/210-int-bezout-witnesses.md).

**Your lane's block (`DONE for this dispatch`, nat-binomial, 2026-08-28).**
Landed the one closeable fact in the `natural-binomial` open set;
the other six open facts in the family are genuinely blocked, not missed.

Of the seven open `natural-binomial` facts (verified all 20 family entries
are `development`, none `held-out`, per `nursery-v1.json`):

- **Closed:** `F:ml430-nat-choose-mono-a1af9c18` (`Nat.choose_mono`,
  `Monotone (fun a => a.choose b)`). Its Monotone unfolding is exactly
  `Nat.choose_le_choose` with arguments `(a, a', c)` permuted so the fixed
  column `c` is outermost — no new induction, just a permuted application.
  `crates/axeyum-lean-kernel/src/nat_prelude/choose.rs::declare_choose_mono`.
  kernel-lean, axiom-free (verified via `theorem_axiom_footprint`).
- **Not actionable, skipped, both definitions confirmed absent from a
  FRESH build (2,006 declarations indexed, `shape_search --include-constructed`,
  exit 1 = ABSENT on both):**
  - `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` — needs `Nat.ascFactorial`
  - `F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` — needs `Nat.descFactorial`
  - `F:ml430-nat-multichoose-one-b210386a` — needs `Nat.multichoose`
  - `F:ml430-nat-multichoose-one-right-7755072d` — needs `Nat.multichoose`
  - `F:ml430-nat-multichoose-zero-right-6ef827c8` — needs `Nat.multichoose`

  Defining `ascFactorial`/`descFactorial`/`multichoose` is a separate task
  (a new `Nat` definition + equation lemmas), out of scope for this dispatch.
- **Not touched, by design:** `F:ml430-mutation-edb05acf07d9ef3f9f8232fc` is
  an outcome-blind mutation fixture (`n.choose n = 0`, deliberately false —
  the real `choose_self` proves `= 1`). It is `open` by construction and has
  no expected truth value; it is not a theorem to close.

`nat_prelude` count: **74 defs + 373 theorems = 447 -> 74 defs + 374 theorems
= 448** (recounted from `theorem_names`/`definition_names`, not hand-incremented).
`the_build_is_deterministic` and `every_nat_declaration_is_checked_and_axiom_free`
both green; full `nat_prelude` sweep 108 passed / 0 failed.

**Next lane:** the five blocked facts need `Nat.ascFactorial`, `Nat.descFactorial`,
and `Nat.multichoose` defined (with their equation lemmas) before they are
reachable at all — that is real new-definition work, not a re-derivation of
something already in the tree.

**Your lane's block (`DONE`, nat-factorial-variants, 2026-08-28).** Task named
three absent definitions blocking five open `F:ml430-nat-*` facts:
`Nat.ascFactorial`, `Nat.descFactorial`, `Nat.multichoose`. Landed the first
one named as the priority ("take descFactorial first ... landing ONE
definition with its boundary lemmas is a complete success"):
`Nat.descFactorial` in `crates/axeyum-lean-kernel/src/nat_prelude/desc_factorial.rs`,
structural recursion on its **second** argument via `NatOps::define_binary`
(the same combinator `Nat.sub`/`Nat.mul` use), so `descFactorial_zero` /
`descFactorial_succ` hold by `Eq.refl`. No fuel device needed, matching the
prediction. Plus two derived boundary theorems: `descFactorial_one`
(`n.descFactorial 1 = n`, closed by `mul_one`'s own proof term against a
purely-defeq goal, no rewrite) and `descFactorial_of_lt`
(`n < k -> n.descFactorial k = 0`, by induction on `k` with `n` held fixed,
explicitly exercising `Nat.sub`'s truncation -- the flagged highest-risk
seam).

`Nat.ascFactorial` and `Nat.multichoose` were **not** attempted this session
(scope discipline per the brief: one definition landed well beats three
started). They remain open/blocked for a future lane.

Measured `nat` trusted surface after this lane:
`nat: axiom=0 opaque=0 quotient=0 total_trusted=0` (`nat_axiom_inventory
--require-axiom-free nat`, exit 0). `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` : 105 passed, 0 failed (confirmed nonzero, up from 104 before
this lane -- one new concrete-instantiation test added). `the_build_is_deterministic`'s
pin recomputed from its own panic message: `74 + 383` -> `75 + 387` (1
definition + 4 theorems added), not hand-counted.

Four new facts created (`F-nat-desc-factorial-{zero,succ,one,of-lt}.json`);
no `F:ml430-*` mirror fact flipped by hand -- those name Mathlib's own
`Nat.descFactorial` and remain untouched, including
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` (the specific fact named
as blocked in the task), which is NOT closed by this lane: the divisibility
theorem (`k! | n.descFactorial k`) needs an induction this session did not
attempt (it is not a simple induction on `k` alone -- the natural argument
needs a Pascal's-rule-shaped step this lane judged out of scope for "one
definition + boundary lemmas"). No target this lane touched carried a
HELD-OUT or MUTATION marker.

**Your lane's block (`DONE for this pass`, nat-primes-2, 2026-08-28).** Closed
five of the ten open `natural-primes` facts, all axiom-free and kernel-checked
in one build (`nat_prelude:: 104/104` after the theorem_names fix, clippy and
rustfmt clean):

- `F:ml430-nat-coprime-primes-5769049f` (`Nat.coprime_primes`) — the target
  the brief called out as unlocking the most. `mp` transports `dvd_refl p`
  along a hypothesised `p = q` to `dvd p q`, then `prime_dvd_iff_not_coprime`'s
  `mp` contradicts the coprimality hypothesis; `mpr` splits
  `coprime_or_dvd_of_prime`, and the `dvd p q` branch applies `q`'s own
  divisor clause to `p`, refuting `p = 1` against `2 ≤ p` and `p = q` against
  the `≠` hypothesis directly.
- `F:ml430-nat-not-prime-of-dvd-of-ne-4ff592c0` — `n`'s own divisor clause
  applied to `m` gives `m = 1 ∨ m = n`; either disjunct contradicts one of the
  two `Not` hypotheses.
- `F:ml430-nat-prime-pred-pos-4e67ac4c` / `F:ml430-nat-succ-pred-prime-4feb123f`
  — both via `pos_implies_succ_pred` (`finite.rs`, cross-file `pub(super)`,
  already used by `binary.rs`/`group.rs`/`fibonacci.rs`) applied to a prime's
  own positivity witness (a locally rebuilt `prime_pos`, mirroring
  `fermat.rs`'s private helper of the same shape byte-for-byte so the built
  `ExprId`s intern identically).
- `F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439` — the OTHER named blocker,
  unblocked by `coprime_primes` as the brief predicted. Composes
  `coprime_primes`'s `mpr` with the already-declared `Nat.coprime_mul_dvd`
  (`crt.rs`); declared after `declare_crt` in the build pipeline for that
  reason.

**Not attempted**: `F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786`.
The named blocker (bounded case split over `p ∈ {2, 3, 4}` plus small-numeral
facts) needs a step this pass didn't build — repeated `two_le_succ_or_eq_one`
/`pred`-peeling down from `2 ≤ p` to pin `p` at 2, 3, or 4, then a "4 is not
prime" refutation. Left open rather than rushed; the five landed already
exceed "landing three is a complete success".

Detail moved to [`../notes/213-nat-primes-2.md`](docs/plan/notes/213-nat-primes-2.md).

**Your lane's block (`DONE`, int-build-time, 2026-08-28). The flagged regression
is NOT in the Int prelude and NOT caused by `bezout_witnesses`.** The reported
`cargo test -p axeyum-lean-kernel --lib int_prelude` going 8.65 s -> 148.28 s is
real as a wall-clock fact about that command, and the cause is entirely outside
`int_prelude/`.

`int_prelude` is a **substring** filter, and
`creal_point::creal_point_tests::cpoint_prelude_builds` matches it —
`cpo` + `int_prelude` + `_builds`. That one test is the whole cost. Measured
with `--report-time --test-threads=1` on the prebuilt
`target/debug/deps/` binary (no cargo lock), `RUST_MIN_STACK` confirmed unset:

| tree | `cpoint_prelude_builds` | all 34/37 `int_prelude::` tests |
| --- | --- | --- |
| `77b71bf10` (08-26, the 34-match "before" tree) | 54.70 s | ~3.0 s |
| `e94d8d080` (parent of the first Bézout commit) | 160.08 s | 3.82 s (34 tests) |
| HEAD (`335da8ba5` + Bézout) | 148.55 s | **4.11 s (37 tests)** |

**The Bézout work costs +0.29 s.** Parent 34 tests / 3.82 s -> HEAD 37 tests /
4.11 s, filtering `int_prelude::` (with the colons, which excludes the
`creal_point` test). Serialized per-test: the two evaluation tests are 0.136 s
and 0.070 s, and the new namespace-inventory test is 0.179 s. **Every one of the
37 `int_prelude::` tests is under 0.72 s.** Nothing in `bezout_witnesses.rs`
approaches the magnitudes that trip the unary-numeral cost documented in
`CLAUDE.md`; the largest `Nat` formed anywhere in the two evaluation tests is 6.

**Where the time actually went, bisected by prelude layer at HEAD:**

- `creal::creal_tests::creal_prelude_builds` — **12.19 s (08-26) -> 108.40 s
  (HEAD)**, an 8.9x growth in two days.
- `cpoint_prelude_builds` is that 108 s plus ~40 s of CPoint layer. The CPoint
  layer itself is flat (42.5 s -> 40.1 s); **all** the growth is in `CReal`.

So the thing to watch is the `CReal` prelude build, which is already a tracked
cost with its own retrospective in `CLAUDE.md` (18.7 s -> 92.6 s from one
declaration, fixed back to 18.4 s). It is now at 108 s again, and no single
`int_prelude` change is involved.

Detail moved to [`../notes/214-int-build-time.md`](docs/plan/notes/214-int-build-time.md).

**Your lane's block (`landed`, nat-bitwise-2, 2026-08-28).**

The frontier (per the prior `207-nat-bitwise` lane, which landed `Nat.bit`)
still had `Nat.bitwise`, `Nat.land`, `Nat.lor`, `Nat.ldiff`, `Nat.bits`
undeclared, blocking the `F:ml430-nat-bitwise-*`/`F:ml430-nat-land-*`/
`F:ml430-nat-lor-*`/`F:ml430-nat-ldiff-*` mirror facts. Per the brief, this
lane's target was one complete definition with boundary lemmas.

**`Nat.land` landed directly, NOT through a general `Nat.bitwise`.** Mathlib
routes `Nat.land := bitwise and`, and `Nat.bitwise` needs a `Bool -> Bool ->
Bool` function argument threaded through mismatched-length base cases
(`m=0`: `if f false true then n else 0`; `n=0`: `if f true false then m else
0`) — substantially more construction than a single lane's scope. `Nat.land`
needs none of that: each bit's AND is the `Nat` **product** of two values
already in `{0, 1}` (`Nat.mod _ 2`), so the recursive step is pure
arithmetic with no `Bool`/`cond` combinator at all — simpler than `Nat.bit`
needed to be.

**The fuel device WAS needed, and it is the exact shape `Nat.logAux`/
`Nat.testBitAux`/`Nat.sizeAux` already use**: structural `Nat.rec` on a fuel
argument, carrying `m`/`n` through and halving them (`Nat.div _ 2`) at each
step:

```
Nat.landAux 0        m n ≡ 0
Nat.landAux (succ f) m n ≡
  if n = 0 then 0
  else if m = 0 then 0
  else 2 * landAux f (m / 2) (n / 2) + (m % 2) * (n % 2)
Nat.land m n := Nat.landAux m m n
```

**The guard order is `n = 0` OUTERMOST**, the mirror of `log.rs`'s `b ≤ n`
ordering and for the identical reason: only the outermost cut collapses the
whole succ-step term with one rewrite, independent of the (possibly
symbolic) fuel predecessor. This makes `land m 0 = 0` an easy induction on
`m` where every step is `refl` with the induction hypothesis unused —
`log_zero_left`'s exact shape. `land 0 n = 0` is even cheaper: fuel is `m =
0`, so the outer `Nat.rec` is already exhausted and the theorem is `refl`
with no induction at all.

Detail moved to [`../notes/215-nat-bitwise-2.md`](docs/plan/notes/215-nat-bitwise-2.md).

**Your lane's block (`DONE`, int-gcd-2, 2026-08-28).** Closed three of the
`integer-gcd` family's remaining open facts, all axiom-free:
`Int.dvd_of_dvd_mul_right_of_gcd_one`, `Int.dvd_of_dvd_mul_left_of_gcd_one`
(both direct corollaries of the already-proved `Int.gauss_lemma`), and
`Int.gcd_greatest` (from the universal property `dvd_gcd`/`gcd_dvd_left`/
`gcd_dvd_right` plus the private `nat_dvd_antisymm` engine `gcd_comm` already
uses). Declarations in `int_prelude/gcd.rs`, wired into `int_prelude.rs`;
`derived_laws` in `int_prelude_tests.rs` recounted 143 -> 146.

**The hand-off claim about `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e` was
NOT attempted this lane** -- it needs genuine `Int`/`Nat` mod-arithmetic
bridging (reduce a Bezout coefficient mod `k` and show the residue lands in
range), a different shape of work than the three closed here, which are all
direct consequences of already-proved divisibility/universal-property lemmas.
Still open, still `train`, no HELD-OUT/MUTATION marker. The remaining
`integer-gcd` open facts (`F:ml430-int-gcd-div-5e01872f`,
`F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`, and the exists-mul-mod-eq-gcd fact
above) are unclaimed for the next lane.

`F:ml430-int-gcd-div-5e01872f` carries a ⚠ NAMED BY
`check-autogenesis-semantic-contract-target-census.py` marker -- checked
before starting: that script pins the fact's `fact_id` only as a label inside
a static Mathlib-source census (`EXPECTED_NARROWEST`), keyed off
`source_content_sha256`/`missing_dependency`/etc., never off this fact's
`epistemic_status`. Closing the fact does not touch what that script checks.

`cargo test -p axeyum-lean-kernel --lib int_prelude` (`--release` for the
`theorem_axiom_footprint` checkers): before this lane 35 passed (per the prior
lane's status note); after, **38 passed, 0 failed**, ~157s. `clippy --all-targets
--all-features -D warnings` and `cargo fmt --check` both clean on the touched
files. `python3 scripts/validate-facts.py`: 0 errors.

**Your lane's block (`WIP`, supon-r6c, 2026-08-28).**

Job 1 (salvage `CReal.meshLevelCount_pow`): **landed, and the prelude
builds green** — but the brief's premise that it was already
kernel-accepted was wrong. Cherry-picking `3c60b3208` alone (without the
symm-argument-order fix that actually lived in the *next* commit,
`ce5b0c29e`) reproduced the original `TypeMismatch`. Applying just that
one-line fix still failed, with `UnboundFVar { id: 17535 }` — the exact
id the previous lane attributed to `hclose_of_uc`. Root cause: in
`declare_mesh_level_count_pow_thm` (`creal/supremum.rs`), the `value`
returned by `d.induct(&motive, &base, &step, j)` was never re-wrapped
with `d.lam_fv(j_fv, nat, value)` to abstract the outer induction target
`j` into a real binder — compare `alternating.rs:383-385`, which does
`let value = d.induct(...); ...; let value = d.lam_fv(k_fv, nat, value);`
for the identical shape. Without that wrap, `ty` is a `Pi` but `value` is
a bare application containing a free `FVar(j_fv)` — an ill-formed pair
that only the kernel's own checker (not `cargo check`) catches. Adding
the missing `lam_fv` wrap fixed it; `creal_prelude_builds` now passes.

Detail moved to [`../notes/217-supon-r6c.md`](docs/plan/notes/217-supon-r6c.md).

**Your lane's block (`done`, creal-build-bisect, 2026-08-28).** The regression
in
[`docs/research/11-design-review/2026-08-28-the-band-is-the-regression.md`](docs/research/11-design-review/2026-08-28-the-band-is-the-regression.md)
is real and it is **not cumulative**. Three files that landed on 2026-08-27
carry **78% of the whole build**, and the mechanism is **not** the
`CReal.integral` `Definition`-unfold one that `CLAUDE.md` names as the first
suspect.

## 1. Both endpoints, measured by this lane

Prebuilt debug test binary run directly (no cargo flock in the number), the
harness's own `finished in`, `RUST_MIN_STACK` confirmed absent from the
environment, `--exact` filter, **1 test** confirmed each time.

| commit | `creal_prelude_builds` | `rat_prelude_builds` | ratio |
|---|---|---|---|
| `77b71bf10` (2026-08-26) | **12.60 s** | 4.85 s | **2.60** |
| HEAD (`1ec0fcec9` + merge) | **105.51 s** | 5.22 s | **20.21** |

8.4x, corroborating the 12.19 → 108.40 s in the write-up. The *reference*
prelude moved 4.85 → 5.22 s (+7.6%) over the same 370 commits, which is what
ordinary growth looks like.

## 2. Where the time is: three files, eight declarations

Detail moved to [`../notes/218-creal-build-bisect.md`](docs/plan/notes/218-creal-build-bisect.md).

**Your lane's block (`DONE`, nat-lor, 2026-08-28).** Landed `Nat.lor`/
`Nat.lorAux` in `nat_prelude/lor.rs`, following `land.rs`'s structural fuel
recursion (`Nat.rec` on the fuel argument), with two design deviations that do
not transfer unchanged from `Nat.land`:

- **Per-bit combinator**: `max (m%2) (n%2)` via the existing `Nat.ble` +
  `bool_select_nat`, not `a + b - a*b` (avoids a `Nat.sub` height dependency
  and its silent-truncation risk, even though truncation cannot actually
  trigger on bit-restricted inputs) and not a bespoke `Bool.rec` cut (more
  construction for the same result). OR of two `{0,1}` values is not their
  product, so `land`'s `mul` shortcut does not transfer at all.
- **Fuel-exhaustion base case**: `lorAux`'s `fuel = 0` row returns `n`, not
  the constant `0` `landAux` uses. Fuel stays `= m` (unchanged from `land`),
  which stays sound because whenever the outer `Nat.rec` on fuel truly
  reaches `0`, the repeatedly-halved `m`-argument is already `0` too (`m`
  always exceeds the `⌊log₂ m⌋ + 1` halvings needed to exhaust it) — but OR
  has no absorbing zero the way AND does, so the base case must return the
  other operand (`n`), not `0`. This is the part of "the shortcut does not
  transfer" that needed actually working out, not just the per-bit formula.
- **Guard order transferred unchanged**: `n = 0` checked OUTERMOST in
  `lorAux`'s succ case (mirrors `landAux`), and it is load-bearing for the
  same reason: `lor_zero_right`'s induction on `m` closes by `Eq.refl` at
  every step (no induction hypothesis forced), because the outermost
  `bool_select_nat` on `n_is_zero` selects the "return `m`" branch without
  forcing the untaken branch where the real recursive step lives.

Landed 3 boundary/sanity theorems (`lor_zero_left`, `lor_zero_right`,
`lor_three_five`), matching the "two or three boundary lemmas is a complete
success" scope. `lor_three_five = 7` is deliberately the same numeral pair as
`land_three_five = 1`, so the two proof terms differ only in the per-bit
combinator and their results are maximally distinguishing.

Detail moved to [`../notes/219-nat-lor.md`](docs/plan/notes/219-nat-lor.md).

**Your lane's block (`DONE this pass`, int-fib, 2026-08-28).** Confirmed
yesterday's `fib-backlog` finding with a fresh positive control (own
`int_theorem_inventory`/`shape_search`-style read of the tree, not a stale
binary): `Int.fib : ℤ → ℤ` genuinely did not exist — `int_prelude/fibonacci.rs`
only ever built `ofNat (Nat.fib n)` terms for `Int.fib_cassini`, never a
function taking a real `Int` argument.

Built `Int.fib` (`int_prelude/fibonacci.rs::declare_fib`): the standard sign
extension `fib(-n) = (-1)^(n+1) fib(n)`, as ONE `Int.rec` case split with no
new recursion device — closer to `Nat.bit` than to `Nat.log`'s fuel device,
exactly as the brief predicted, confirmed rather than assumed (`Int.pow` is
already total/structural on its `Nat` exponent, so no parity case-split is
needed inside the definition itself):

- `fib (ofNat n)   := ofNat (Nat.fib n)`
- `fib (negSucc m) := pow (neg one) m * ofNat (Nat.fib (succ m))`

Closed one fact: `F:ml430-int-fib-two-mul-add-one-pos-8977f65f`
(`∀ n : ℤ, 0 < Int.fib (2*n+1)`), landed as
`Int.fib_two_mul_add_one_pos` — positivity at every ODD index in EITHER
direction of `ℤ`. Case split on `n`; in both branches `2*n+1` reduces PURELY
(no named lemma for the arithmetic itself — `Int.mul`/`Int.add` on
`ofNat`/`ofNat` and `ofNat`/`negSucc` pairs, and `Int.subNatNat`'s own
`Nat.sub`-based case split, are all structural, `defs.rs`'s own module doc)
down to a clean `Nat`-side shape. The `ofNat` branch closes directly from
`Nat.fib_pos_of_pos` + `Nat.zero_lt_succ` via the kernel's own defeq (`Int.lt`
on `ofNat`/`ofNat` reduces to `Nat.lt`, already documented elsewhere in this
codebase). The `negSucc j` branch needed exactly one non-structural fact,
`(-1)^(2j) = 1` (new private helper `pow_neg_one_two_mul`, induction on `j`
reusing `pow_neg_one_succ` + `neg_neg` — both already built for
`fib_cassini`), then an `Int`-level `itransport` moves the resulting
`Nat`-side positivity fact across `Eq Int (fib (negSucc (2j))) (ofNat
(Nat.fib (2j+1)))`.

Detail moved to [`../notes/220-int-fib.md`](docs/plan/notes/220-int-fib.md).

**Your lane's block (`WIP`, nat-modeq-gcd, 2026-08-28).** Six open facts across
two small families (all `development`, none HELD-OUT/MUTATION, verified against
a fresh `scripts/fact-frontier.py` run before touching anything):
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`,
`F:ml430-nat-coprime-of-dvd-6f652673`,
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`,
`F:ml430-nat-div-dvd-div-left-b56f6f7c`,
`F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`,
`F:ml430-nat-modeq-gcd-eq-5167ff4f`.

Landed `Nat.ModEq.gcd_eq` (`F:ml430-nat-modeq-gcd-eq-5167ff4f`) in
`nat_prelude/gcd.rs` as `declare_modeq_gcd_eq`, dispatched after
`declare_dvd_antisymm` (needs `dvd_antisymm`, `gcd_dvd_left/right`, `dvd_gcd`,
`dvd_add`, `dvd_add_iff_right`, `dvd_mul_right_of_dvd`, `add_comm`). Route:
eliminate the balanced-witness `modEq m a b := ∃ u v, a+m*u=b+m*v` twice, show
`gcd a m ∣ gcd b m` and the mirror image, close with `dvd_antisymm`. Kernel
accepted first attempt; `every_nat_declaration_is_checked_and_axiom_free`
caught the missing `theorem_names` entry (recounted, not incremented: 400).
`nat_prelude::` sweep: 110 passed, 0 failed (was 109 before).

Two of the six are judged genuinely out of scope for this lane, both because
they need a NEW predicate/definition the whole kernel lacks, confirmed absent
by grep across `nat_prelude.rs` and every `nat_prelude/*.rs`:
- `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` needs `IsRelPrime` (per the
  brief; agreed after independent check).
- `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` needs `Nat.minFac` (least prime
  factor) — **not previously flagged, newly confirmed absent this session**.
  `exists_prime_dvd`/`least_divisor_search` give existence of *a* prime
  factor, not a computable minFac with defining equations; building one is a
  separate, larger task.

Detail moved to [`../notes/221-nat-modeq-gcd.md`](docs/plan/notes/221-nat-modeq-gcd.md).

**Your lane's block (`DONE`, nat-asc-multichoose, 2026-08-28).** Both
definitions landed with boundary lemmas, evaluation tests, and six new
`F:nat-*` facts.

`Nat.ascFactorial` mirrors `Nat.descFactorial` exactly (`NatOps::define_binary`,
structural recursion on the second argument), climbing with `Nat.add` instead
of descending with truncated `Nat.sub`. `ascFactorial_zero`/`_succ` hold by
`Eq.refl` (no fuel device); `ascFactorial_one` reduces to `Nat.mul_one`'s own
proof term, exactly like `descFactorial_one` reduces to it.

`Nat.multichoose n k := choose (pred (add n k)) k` is a plain non-recursive
abbreviation over already-declared `Nat.add`/`Nat.pred`/`Nat.choose` — not a
fresh recursion. `multichoose_zero_right` needs no reduction at all
(`choose_zero_right` holds for any first argument); `multichoose_one_right`
reduces fully by ι alone (`add n 1 ≡ succ n`, `pred (succ n) ≡ n`, then
`choose_one_right` closes it — no lemma beyond that one); `multichoose_one`
is the one genuinely needing a `congr`/`trans` chain, because `Nat.add`
recurses on its RIGHT argument and the literal `1` sits on the LEFT
(`add 1 k` stuck for symbolic `k` — bridged via `succ_add`/`zero_add`).

Every definition carries a concrete-instantiation evaluation test with a
negative control catching the copy-paste class of bug the kernel's trusted
gate cannot see (a `Definition` type-checks whatever it computes):
`asc_factorial_evaluates_correctly` checks `3.ascFactorial 2 = 12` against a
DESCENDING-product control (`3*2=6`, and `3.descFactorial 2`) that an
`add`/`sub` swap would still type-check but compute; `multichoose_evaluates_correctly`
checks `3.multichoose 2 = 6` against the `pred`-dropped value `10` a copy-paste
omitting `- 1` would compute.

Measured: `nat: axiom=0 opaque=0 quotient=0 total_trusted=0`
(`nat_axiom_inventory --require-axiom-free nat`) — the eight new declarations
(2 definitions — `ascFactorial`, `multichoose` — plus 6 theorems —
`ascFactorial_zero/_succ/_one`, `multichoose_zero_right/_one/_one_right`)
add zero axioms. `nat_prelude::` suite: 109 passed, 0 failed (was 107 before
this lane). `cargo fmt --check` and
`clippy --all-targets --all-features -D warnings` both clean.

Detail moved to [`../notes/222-nat-asc-multichoose.md`](docs/plan/notes/222-nat-asc-multichoose.md).

**Your lane's block (`DONE this pass`, cas-reconstruct, 2026-08-28).**

`scripts/validate-facts.py`, before and after, run in this worktree:

```
cas-certificate: 29 total -- kernel-reconstructed 1, cas-internal 28
cas-certificate: 31 total -- kernel-reconstructed 3, cas-internal 28
```

**Nothing was relabelled and no checker was weakened.** The two new
`kernel-reconstructed` rows are CAS → kernel bridge tests that were authored,
passed, and were never registered in the ledger:

- `F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve` —
  `rat_prelude::cas_ivt_bridge_tests::tests::ivt_sign_bracket_degree_four_kernel_checked`,
  `x^4-2` on `(1,2)`. `F:cas-ivt-sign-bracket-cbrt2-kernel-checked`'s own notes
  already cited this fact id; the fact did not exist.
- `F:cas-difference-of-squares-free-x-kernel-checked` —
  `complex::cas_bridge_tests::cas_verified_difference_of_squares_true_and_false`,
  `(x+1)(x-1) = x^2-1` at a **free** `x`, plus the CAS-refuted variant rejected
  by the same kernel.

Both were re-run here (1 passed each; 5.51 s and 123.77 s), and their
`checker_command`s were executed **verbatim, with `/usr/bin/grep`**, each
returning a count of `1`.

**The degree-4 kernel check was mutation-verified by this lane rather than
taken on the authoring lane's word.** Changing only the kernel-side bound from
the exact `14` to a wrong-but-true-looking `16` — `Nat.le 1 16` is itself a
true proposition, just not the one the reduced term inhabits — makes
`Kernel::add_declaration` reject with
`TypeMismatch { expected: ExprId(1577225), got: ExprId(1577239) }` and the test
FAIL; reverted, it passes again. So the kernel term asserts *what the CAS
computed* (`p(2) = 14`), not merely something well-typed. The mutation was made
and reverted inside this lane's own worktree, and `git status` was confirmed
clean afterwards.

Detail moved to [`../notes/223-cas-reconstruct.md`](docs/plan/notes/223-cas-reconstruct.md).

**Your lane's block (`DONE this pass`, evt-endpoint, 2026-08-28).**

The previous lane (`223-cas-reconstruct`) sized this as needing no new kernel
machinery: `docs/plan/status/223-cas-reconstruct.md`'s "Next lane" item 1. That
sizing HELD, verified rather than trusted:

- `q = p - p(-3)` (coefficients `[9,-6,0,1]`), `r = p - p(2)`
  (`[4,-6,0,1]`) for `p = x^3-6x`. `q(-1) = 14`, `r(-1) = 9`, exactly the
  constants the previous lane's write-up sized.
- Both admitted through `crate::Kernel::add_declaration` using the EXISTING
  `zero_lt_via_nat_le` engine (`rat_prelude/cas_ivt_bridge_tests.rs`) — no new
  `rat_prelude` lemma, kernel primitive, or proof pattern.

`scripts/validate-facts.py`, `cas-certificate` split, before/after (this
worktree):

```
before: cas-certificate: 31 total -- kernel-reconstructed 3, cas-internal 28
after:  cas-certificate: 32 total -- kernel-reconstructed 4, cas-internal 28
```

**What was built.** `crates/axeyum-lean-kernel/src/rat_prelude/cas_evt_bridge_tests.rs`
(new file, wired via `#[cfg(test)] mod cas_evt_bridge_tests;` in
`rat_prelude.rs`), one test:
`rat_prelude::cas_evt_bridge_tests::tests::evt_endpoint_exclusion_kernel_checked`.
It:

Detail moved to [`../notes/224-evt-endpoint.md`](docs/plan/notes/224-evt-endpoint.md).

**Your lane's block (`DONE`, nat-factorial-dvd, 2026-08-28).** Both
`F:ml430-nat-factorial-dvd-descfactorial-bbf6124f` and
`F:ml430-nat-factorial-dvd-ascfactorial-44a4e641` are closed — the brief's
"landing the choose bridge plus ONE divisibility fact" bar was cleared twice
over.

`Nat.descFactorial_eq_factorial_mul_choose : n.descFactorial k = k! * n.choose k`
did not exist anywhere in the kernel before this session (confirmed by
reading `choose.rs`/`binomial.rs`/`desc_factorial.rs` in full — no
`descFactorial`-to-`choose` cross-reference existed, and both target facts'
own `open` status recorded the bridge as the deferred prerequisite). It is
the real deliverable: proved by induction on `n`, `k` generalized inside the
motive (mirroring `succ_mul_choose_eq`'s own outer-induction shape), using a
new front-peel identity `Nat.descFactorial_succ_eq_succ_mul : (succ n).descFactorial
(succ k) = succ n * n.descFactorial k` (a separate, simpler induction on `k`
with `n` held fixed) to bridge the outer IH — which is only ever about `n`,
never `succ n` — into the successor step. The successor step's `k = succ j`
case chains six identities: the front-peel lemma, the outer IH at `j`,
`mul_left_comm` (newly promoted `pub(super)` in `binomial.rs`, was file-private
to it), `Nat.succ_mul_choose_eq`, `mul_assoc` (reversed), `factorial_succ`
(reversed). `factorial_dvd_descFactorial` then falls out immediately:
`Nat.dvd_mul : a ∣ a*q` transported along the bridge equation.

Detail moved to [`../notes/225-nat-factorial-dvd.md`](docs/plan/notes/225-nat-factorial-dvd.md).

**Your lane's block (`DONE`, nat-ldiff, 2026-08-28).** Landed `Nat.ldiff`/
`Nat.ldiffAux` in `nat_prelude/ldiff.rs`, following `land.rs`'s/`lor.rs`'s
structural fuel recursion (`Nat.rec` on the fuel argument, `ldiffAux m m n`).

**Worked out the absorbing-zero asymmetry on paper before writing kernel
terms, exactly as the `lor` lane did.** `Nat.ldiff m n` (bitwise "`m` AND NOT
`n`") has an absorbing zero on exactly ONE side: `ldiff 0 n = 0`, but
`ldiff m 0 = m`, not `0`. That determined every shape choice:

Detail moved to [`../notes/226-nat-ldiff.md`](docs/plan/notes/226-nat-ldiff.md).

**Your lane's block (`DONE`, nat-bitwise-general, 2026-08-28).** `Nat.bitwise`
landed: `crates/axeyum-lean-kernel/src/nat_prelude/bitwise.rs` (new file),
wired into `nat_prelude.rs` (mod/use/fields/initializers/call site) and
`nat_prelude/nat_prelude_tests.rs`.

**The two earlier declines do NOT hold anymore, and here is the precise
reading of what "mismatched-length base cases" costs.** Both prior lanes
declined citing "a `Bool -> Bool -> Bool` function threaded through
mismatched-length base cases" as too big for one lane. That threading turns
out to be small and mechanical once `land`/`lor`/`ldiff` exist: the general
base case answers "does the fuel operand carry this operator's absorbing
zero?" — a question with no fixed answer for a general `f` — by evaluating
`f` at the two boundary `Bool` literals (`f false true`, `f true false`) and
gating with the SAME `bool_select_nat` combinator `land`/`lor`/`ldiff` already
build for their own zero-guards. No new primitive, no new height dependency.
The per-bit step needs one genuinely new piece (`Nat.beq _ 1` to get a `Bool`
out of each `{0,1}` bit, apply `f`, `bool_select_nat` back to `{0,1}`), also
mechanical.

**Outcome 1 landed** (of the brief's three ranked outcomes): `Nat.bitwise`
+ `Nat.bitwiseAux` (fuel-recursive, `f` threaded through every closure), two
`f`-general boundary theorems (`bitwise_zero_left` refl, `bitwise_zero_right`
induction — the ONE genuinely new proof-content wrinkle: the base case needs
a small `Bool`-case-split helper, `bool_select_same`, that the three
specializations' own zero-right theorems never needed, because their base
cases were syntactically identical for a fixed `f`), and three concrete
specialization checks (`bitwise and_fn 3 5 = land 3 5`, `bitwise or_fn 3 5 =
lor 3 5`, both refl against the ACTUAL sibling declaration; `bitwise xor_fn
3 5 = 6` against a hand-computed numeral, no XOR sibling exists).

Detail moved to [`../notes/227-nat-bitwise-general.md`](docs/plan/notes/227-nat-bitwise-general.md).

**Your lane's block (`DONE for this pass`, fib-2, 2026-08-28).** Landed
`Nat.le_fib_self`, kernel-checked and axiom-free, closing
`F:ml430-nat-le-fib-self-0cbccb4d`. This satisfies the brief's "land either
`Int.fib_add` or the `Nat.le_fib_*` chain is a complete success" bar.

What did NOT land, and why (each blocker re-verified against the tree
before being reported, per the brief's "a lane refuted another lane's
hand-off yesterday" warning):

Detail moved to [`../notes/228-fib-2.md`](docs/plan/notes/228-fib-2.md).

**Your lane's block (DONE, int-parity, 2026-08-28).** Landed `Int.Even`/`Int.Odd`
(`int_prelude/parity.rs`, new module), defined as `Nat.Even`/`Nat.Odd (natAbs n)`
rather than a fresh `Int`-level existential — magnitude alone decides parity,
and this composes for FREE with `natAbs`'s pure reduction on both `Int.rec`
constructors (confirms the earlier lane's prediction exactly). Two bridge
theorems (`odd_iff_nat_abs_odd`, `even_iff_nat_abs_even`, both near-tautological
`fun h => h` proofs) and `Int.fib_of_odd` (`int_prelude/fibonacci.rs`) all landed
and are kernel-checked with empty axiom footprints. `Int.fib_of_odd`'s ofNat
branch is free (unused hypothesis, both sides reduce to the same term); the
negSucc branch needed one new induction, `pow_neg_one_add_self` (same technique
as the file's existing `pow_neg_one_two_mul`, over the `k+k` witness shape
`Nat.Even` uses instead of `mul 2 k`, since `add(succ k)(succ k)` does not
reduce purely the way `mul two (succ k)` does — bridges via an explicit
`succ_double_eq_nat` equation lifted to `Int`). No new `Int`-level parity lemma
was needed for the proof itself, exactly as predicted.

Concrete instantiation tests with genuine positive AND negative witnesses at
BOTH signs (`Int.Odd 3`/`-3` inhabited, `Not (Int.Odd 4)`/`-4` proved) —
`int_odd_applies_at_concrete_values_of_both_signs`,
`fib_of_odd_applies_at_a_concrete_odd_index_of_each_sign`
(`int_prelude_tests.rs`). `int_prelude::` test count: 38 -> 40 (all pass).
`derived_laws` 147 -> 150, `definition_names` 25 -> 27 (pinned arrays,
recounted not incremented). `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both clean.
`python3 scripts/validate-facts.py`: 0 errors, 1913 facts.

New facts: `F:int-even`, `F:int-odd` (the two definitions), `F:int-odd-iff-nat-abs-odd`,
`F:int-even-iff-nat-abs-even` (the bridge theorems). `F:ml430-int-fib-of-odd-66560495`
flipped `open` -> `proved` with a real kernel-checked proof (not a mirrored
transcription of Mathlib's tactic proof, which was never consulted).

Next lane: nothing else in this task's scope is open. `Int.Even`'s own bridge
theorem (`even_iff_nat_abs_even`) has no consumer yet — it was built for a
symmetric, discoverable API pair per the brief, not because anything currently
needs it.

**Your lane's block (`DONE for this pass`, nat-bounded-cases, 2026-08-28).**
Built the requested eliminator and landed BOTH facts it was meant to unblock
— the brief's bar was "the eliminator plus ONE fact", so this is over that
bar, not merely at it.

- **`ops::cases_lt_bound`** (`nat_prelude/ops.rs`): `∀ n, Lt n bound → …`,
  peeled one numeral at a time via `le_of_lt_succ` + `lt_or_eq_of_le` (the
  same two lemmas `two_divisor_dichotomy`'s 2-way version already used),
  bottoming out at `bound == 1` via `zero_le` + `le_antisymm` rather than
  ever deriving the impossible `Lt n 0`. Branches each prove a STATIC fact
  at the literal `i`, transported up to `n` — the right shape when the
  conclusion genuinely varies with `n` (a computed property true at every
  point).
- **`ops::cases_lt_or_ge`**: splits a goal at a threshold `b` via
  `Nat.lt_or_ge n b`, handing off to separate `Lt n b` / `Le b n` handlers.
- **`ops::cases_lt_bound_absurd`**: the complementary shape discovered while
  proving the SECOND fact — a FIXED goal (doesn't vary with `n`), each
  branch instead receiving the witnessing equality `Eq n i` to derive a
  contradiction from an outer hypothesis about `n`. `cases_lt_bound`'s
  branches cannot do this (they prove `motive(i)` in isolation, with no
  access to `n`'s own hypotheses), so this needed to be a second combinator,
  not a parameter on the first. Also verified this shape reduces to only
  `le_of_lt_succ`/`lt_or_eq_of_le`/`zero_le`/`le_antisymm` — no `False.rec`
  needed even at the `bound == 1` base case.

Both closed facts:

Detail moved to [`../notes/230-nat-bounded-cases.md`](docs/plan/notes/230-nat-bounded-cases.md).

**Your lane's block (`DONE`, nat-descfact-lemmas, 2026-08-28).** All four
target facts landed: `descFactorial_self`, `descFactorial_le`,
`self_le_factorial` (all new proofs), and `descFactorial_of_lt` (a status
flip — the declaration already existed and already stated the fact's
`formal.statement` verbatim; nothing needed but evidence + the status flip).
`descFactorial_eq_factorial_mul_choose` (landed by a prior lane) was the main
tool for the first two; `self_le_factorial` is a direct induction,
independent of that bridge. Skipped `F:ml430-mutation-7afa5ec620720a1501bf349d`
per brief (a deliberately-perturbed negative control in this family).

Kernel gate: `cargo test -p axeyum-lean-kernel --lib nat_prelude` — 119
passed, 0 failed (was 116 before this lane; +3 new theorems +1 test — see
below). `python3 scripts/validate-facts.py`: 0 errors, `open` 85 -> 84,
`proved` 1824 -> 1825. `cargo fmt`/`clippy --all-targets` clean on the
touched files.

Nothing was kernel-rejected. Every proof term type-checked on the first
attempt against `Kernel::add_declaration`; no misdiagnosis, no bisect
needed. `nat_prelude` inventory count (`definition_names`/`theorem_names`
sum, `the_build_is_deterministic`'s own pin): 85+429=514 before this lane,
85+432=517 after (+3 theorems: `descFactorial_self`, `descFactorial_le`,
`self_le_factorial`; 0 new definitions). Both increments were read off the
test's own panic message, never hand-counted.

**Your lane's block (`DONE`, nat-multichoose-facts, 2026-08-28).** The three
target facts (`F:ml430-nat-multichoose-zero-right-6ef827c8`,
`F:ml430-nat-multichoose-one-b210386a`,
`F:ml430-nat-multichoose-one-right-7755072d`) and the `Nat.multichoose`
theorems they mirror had already landed the day before this lane started
(`nat_prelude/multichoose.rs`, three `declare_multichoose_*` theorems, the
paired local facts `F-nat-multichoose-zero-right.json` /
`F-nat-multichoose-one.json` / `F-nat-multichoose-one-right.json`, all
`proved`). This lane's job was the judgement the definition lane had already
made but that this brief asked to be checked independently: **does our
`Nat.multichoose` match Mathlib's, so the `ml430` mirrors could honestly be
flipped instead of staying as separate local facts?**

**Verdict: no — confirmed by reading Mathlib's actual source, not by prose.**
Fetched `Mathlib/Data/Nat/Choose/Basic.lean` at the pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0). Mathlib's `multichoose`
is a genuine three-case double recursion (Pascal-triangle style):

```lean
def multichoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => multichoose n (k + 1) + multichoose (n + 1) k
```

and `multichoose_eq : multichoose n k = (n + k - 1).choose k` is a **proved
theorem** about that recursion, not the definition. Our `Nat.multichoose` is
defined *directly* as that formula (`choose (pred (add n k)) k`) — i.e. we
define as a body what Mathlib proves as a theorem about a structurally
different function. This is the same shape as the `Nat.log`/`sqrt`/`clog`
caution the brief pointed at (fuel/formula construction vs. Mathlib's own
recursion), not the "literally the same function" case — so the "never flip
a mirror when the construction differs" rule was necessary here, and the
definition lane's decision (recorded in the three local facts' `notes`) was
correct. All three `ml430` facts remain `epistemic_status: open`, untouched
— per the log/sqrt precedent (`F-ml430-nat-log-le-self-da387172.json`), a
declined mirror keeps its original boilerplate `notes`, and the reasoning
lives in the paired local fact instead.

Detail moved to [`../notes/232-nat-multichoose-facts.md`](docs/plan/notes/232-nat-multichoose-facts.md).

**Your lane's block (`DONE`, nat-rec-agreement, 2026-08-29).** The boundary two
lanes stopped at is crossed. Six declarations landed, kernel-admitted on the
FIRST attempt, `nat` still `axiom=0 opaque=0 quotient=0`.

Machinery, in `nat_prelude/ops.rs` beside the other eliminators:

- `cases_mod_two` — the `Nat.mod _ 2 ∈ {0,1}` split `bitwise.rs` named as
  absent, as an eliminator over a motive that VARIES with the remainder. It is
  `cases_lt_bound` at `bound = 2` fed `mod_lt`'s witness. **It genuinely did
  not exist**: `powsq.rs`'s *private* `mod_two_eq_one_of_ne_zero` gives only
  the `= 1` half and needs `r ≠ 0` already in hand, and `Nat.even_or_odd` is
  `div`-shaped and never mentions `Nat.mod`.
- `agree_by_fuel_induction` — induction on a shared fuel counter with **both**
  value arguments generalized in the motive. The brief predicted this
  generalization would be the entire difficulty. It was.

Declarations, in a new `nat_prelude/rec_agreement.rs` (the theorems mention
`Nat.bitwise` *and* a sibling, so neither module owns them):

| name | statement |
| --- | --- |
| `Nat.lt_two_cases` | `∀ r, Lt r 2 → Or (Eq r 0) (Eq r 1)` |
| `Nat.mod_two_eq_zero_or_one` | `∀ n, Or (Eq (mod n 2) 0) (Eq (mod n 2) 1)` |
| `Nat.bitwise_aux_eq_land_aux` | `∀ fuel m n, Eq (bitwiseAux and_fn fuel m n) (landAux fuel m n)` |
| `Nat.bitwise_aux_eq_lor_aux` | `∀ fuel m n, Eq (bitwiseAux or_fn fuel m n) (lorAux fuel m n)` |
| `Nat.bitwise_and_eq_land` | `∀ m n, Eq (bitwise and_fn m n) (land m n)` |
| `Nat.bitwise_or_eq_lor` | `∀ m n, Eq (bitwise or_fn m n) (lor m n)` |

Facts: `F:nat-mod-two-eq-zero-or-one`, `F:nat-bitwise-and-eq-land`,
`F:nat-bitwise-or-eq-lor`. The two `_three_five` predecessors are kept (they
are *reduction*-based, independent of the induction) with their now-stale
"was NOT attempted" notes corrected in place rather than deleted, and
`bitwise.rs`'s module doc likewise.

Detail moved to [`../notes/233-nat-rec-agreement.md`](docs/plan/notes/233-nat-rec-agreement.md).

**Your lane's block (`DONE for this pass`, int-gcd-div, 2026-08-29).** One of
three facts landed, fully kernel-checked; the other two are re-scoped open
with a concrete, verified reason each — not "hard", a named missing lemma.

**Landed: `F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`
(`Nat.exists_mul_mod_eq_gcd`).** The second-lane refutation in the brief
("this needs genuine Int/Nat mod-arithmetic bridging, not a corollary of the
Bezout witnesses") held under my own construction: `declare_exists_mul_mod_eq_gcd`
(`crates/axeyum-lean-kernel/src/int_prelude/gcd.rs`) reduces the Bezout
coefficient `Nat.gcdA n k` modulo `k` through `Int.modEq_add_mul_left` /
`Int.ModEq.mul_left` / `Int.mod_modEq` / `Int.ModEq.symm` (all pre-existing in
`modeq.rs`/`modeq_family.rs`) plus one call to `super::wilson::emod_eq_self_of_in_range`
(already `pub(super)`), then descends the resulting `Int` equation to the
stated `Nat` equation via `natAbs`. No new axiom, no infrastructure change
outside `gcd.rs` + one `IntPrelude` field + one build-order line. Verified:
`cargo test -p axeyum-lean-kernel --lib int_prelude::` — 40 passed, including
`every_int_declaration_is_checked_and_axiom_free` and
`derived_laws_have_no_axiom_footprint` — plus the fact's own
`theorem_axiom_footprint` grep checker, both run by hand before landing.
`cargo fmt --edition 2024 --check` and `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` both clean. `python3 scripts/validate-facts.py`:
0 errors.

**Not landed, re-scoped open, both for the SAME underlying reason:**

Detail moved to [`../notes/234-int-gcd-div.md`](docs/plan/notes/234-int-gcd-div.md).

**Your lane's block (`DONE`, nat-bitwise-facts, 2026-08-29).** Full triage of
all 19 `natural-bitwise` facts (per `nursery-v1.json`'s `family` field, which
is the authoritative 19 — `check-development-partition.py` and the
2026-08-27 curriculum doc both cite 19 for this family). **Zero facts closed**
— every one of the 18 real targets needs either a file outside this lane's
scope (`bitwise.rs`, owned by a sibling Opus lane right now; `binary.rs`,
never granted) or the fuel-irrelevance/bit-peeling machinery the CLAUDE.md
brief explicitly says not to duplicate. The 19th is a flagged MUTATION,
skipped per instructions. No `nat_prelude` source file was touched;
`nat_prelude` D+T count is unchanged at 85+432 (pinned in
`nat_prelude_tests.rs::the_build_is_deterministic`) before and after.

**Triage table (all 19):**

Detail moved to [`../notes/235-nat-bitwise-facts.md`](docs/plan/notes/235-nat-bitwise-facts.md).

**Your lane's block (`DONE for this pass`, int-gcd-div-2, 2026-08-29).**
`F:ml430-int-gcd-div-gcd-div-gcd-2db608dc` (`Int.gcd_div_gcd_div_gcd`) is
CLOSED. `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) is confirmed genuinely
absent and re-scoped open with a precise statement of the missing piece — not
attempted, per the "assess, do not assume" brief.

**Closed: `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`.** The prior
`int-gcd-div` lane's handoff (`docs/plan/status/234-int-gcd-div.md`) had
worked out a complete independent Bézout route (not routed through
`Int.gcd_div`, since that lemma doesn't exist) and stopped one step short at
"`Nat.mul g 1` gets stuck at `Nat.add Nat.zero g` for symbolic `g`, needs an
explicit `Nat.mul_one`-style lemma I did not verify against the kernel."

**The handoff's sizing of the stuck point was slightly off, but the fix was
exactly what it named.** The actual construction never needs `Nat.mul_one`
or `Nat.add`/`Nat.zero_add` at all — the stuck term the handoff described
would arise from a NAT-level `g*1` reduction attempt, but the route I built
never reduces at the `Nat` level for this step. Instead: `Int.mul_one(c) :
Eq Int (c*one) c` (an existing lemma taking the multiplicand symbolically,
already used pervasively elsewhere in `int_prelude`) closes `c*1 = c`
directly at the `Int` level, and the subsequent `natAbs`/
`Nat.mul_left_cancel_of_pos` cancellation is what actually descends to `Nat`
— at which point the shared factor is `natAbs c` (defeq to `g`), not a raw
`g*1` term that needs reducing. So the predecessor correctly named the RIGHT
FAMILY of lemma (`Nat.mul_one`) and the right general shape of the problem
(a stuck `Nat.add`/`succ` reduction is this repo's most-documented gotcha),
but the actual proof route I built sidesteps the specific stuck term by doing
the `c*1=c` step at `Int`, not `Nat`.

Full route (`declare_gcd_div_gcd_div_gcd`,
`crates/axeyum-lean-kernel/src/int_prelude/gcd.rs`): with `g := gcd i j`,
`c := ofNat g`, `qi := i.ediv c`, `qj := j.ediv c`, `u := gcdA i j`,
`v := gcdB i j`, `X := qi*u + qj*v`:

Detail moved to [`../notes/236-int-gcd-div-2.md`](docs/plan/notes/236-int-gcd-div-2.md).

**Your lane's block (`DONE (one auxiliary; transport sized)`, nat-fuel-irrelevance, 2026-08-29).**
Fuel-irrelevance landed for `landAux`, kernel-admitted on the corrected
attempt (one direction bug, see below). None of the 7 blocked facts
(`land_comm`, `land_assoc`, `land_bit`, `lor_comm`, `lor_assoc`, `lor_bit`,
`ldiff_bit`) closed this session — see "What is still needed" for why that is
a separate, larger piece of work than fuel-irrelevance itself, and why the
brief's second acceptance criterion ("fuel-irrelevance for one auxiliary,
with transport to the others sized") is what this lane delivers.

**The statement, and why this hypothesis.** In `nat_prelude/rec_agreement.rs`:

```
Nat.land_aux_eq_land_of_le :
  ∀ fuel m n, Le m fuel → Eq (landAux fuel m n) (land m n)
```

`Le m fuel`, not an unconditional statement: the canonical call
`landAux m m n` puts `m` in the fuel slot and the recursion halves the value
argument every step, so a caller unfolding at a NON-canonical fuel (e.g.
`fuel = bit a m`, `land_bit`'s shape) always has MORE fuel than canonical,
never less — but `landAux 0 m n` for `m > 0` is genuinely `0` while
`land m n` need not be, so the statement is false without some sufficiency
hypothesis. Weaker alternatives were considered and rejected:

- No hypothesis at all: false (the `m > 0`, `fuel = 0` counterexample above).
- `Eq m fuel` (only the canonical fuel): true but useless — it says nothing
  about the very case the 7 facts need, fuel strictly above canonical.

**Which side proved, and why the transport is NOT free (correcting the
brief's framing).** The brief's suggested route was `agree_by_fuel_induction`
inducting on `fuel` alone, generalizing `m`/`n`. That route hits a
self-reference: `land m n` unfolds to `landAux m m n`, which puts the SAME
value `m` in the fuel slot, so relating it to `landAux (succ k) m n` (`k`
from the induction) needs `landAux m m n` to unfold via `m`'s own shape —
and once `m = succ predecessor` is exposed, the recursive call on THAT side
is at fuel `predecessor`, a value the induction's own hypothesis (fixed at
fuel `k`) says nothing about.

The fix, landed here: generalize over BOTH fuels at once
(`ops::agree_by_double_fuel_induction`, a new 3-value-generalized sibling of
`agree_by_fuel_induction`):

Detail moved to [`../notes/237-nat-fuel-irrelevance.md`](docs/plan/notes/237-nat-fuel-irrelevance.md).

**Your lane's block (`DONE`, int-two-sided-induction, 2026-08-29).** The stated
deficiency — "no two-sided (`ofNat`/`negSucc`-covering) induction combinator
exists anywhere in `int_prelude/`" — is closed, and so is the keystone it
blocked. Three declarations landed, all axiom-free, **all three accepted by the
kernel on the first attempt; nothing was rejected in this lane.**

- `Int.induction_on` (`int_prelude/two_sided_induction.rs`) —
  `∀ P, P 0 → (∀ n, P n → P (n+1)) → (∀ n, P n → P (n-1)) → ∀ n, P n`.
- `Int.fib_rec` (`int_prelude/fibonacci.rs`) — `fib (n+2) = fib (n+1) + fib n`
  at **every** integer index.
- `Int.fib_add` (`int_prelude/fibonacci.rs`) — Mathlib's statement verbatim,
  `fib (m+n) = fib (m-1) * fib n + fib m * fib (n+1)`.

`int_prelude::` went **40 → 44 passing**, `derived_laws` 151 → 154, integer
trusted surface still 0.

**The question the brief asked: `Int.fib_add` did NOT reduce to `Nat.fib_add`
plus sign bookkeeping.** `Nat.fib_add` (`fib (succ (m+n)) = fib m * fib n +
fib (succ m) * fib (succ n)`) is exactly this statement restricted to
`m ≥ 1, n ≥ 0` — one of four constructor pairs, and not even all of the
non-negative case: at `m = 0` the leading coefficient is `fib(-1)`, a value at a
negative index. The proof uses `Nat.fib_add` nowhere.

**But the combinator was CHEAP, against the prior sizing of "genuinely
comparable-or-more effort than the theorem it blocks".** ℤ's operations are
nested `Int.rec` over ℕ, so at a *constructor* argument every bridging step
computes, and no equation lemma is needed anywhere:

| step | reduces to | why |
| --- | --- | --- |
| `add (ofNat k) one` | `ofNat (succ k)` | `Nat.add` recurses right and the right argument is the literal `1` |
| `sub zero one` | `negSucc 0` | `Int.sub` is a plain `Definition`; `subNatNat` scrutinises the closed `Nat.sub 1 0` |
| `sub (negSucc k) one` | `negSucc (succ k)` | again the literal is on the right |

Detail moved to [`../notes/238-int-two-sided-induction.md`](docs/plan/notes/238-int-two-sided-induction.md).

**Your lane's block (`DONE`, nat-fuel-transport, 2026-08-29).** Both
transports landed (`lorAux`, `ldiffAux`), and `F:ml430-nat-land-comm-7e6ad72e`
(one of the 7 `natural-bitwise` facts fuel-irrelevance was blocking) is
closed. The other 6 (`land_assoc`, `land_bit`, `lor_comm`, `lor_assoc`,
`lor_bit`, `ldiff_bit`) remain open — see "What is still needed" below for
what each still needs beyond this lane's work.

**Whether the ~20-lines-each sizing held.** No — it undercounted both, and
in different ways.

- **`lorAux`'s transport needed a piece the handoff did not name.**
  `Nat.lor_aux_zero_left_any_fuel`'s `succ`-branch proof cannot use
  `bool_select_nat_same` the way `land`'s analogue does: at `m = 0` fixed,
  `fuel = succ f`, the outer `n = 0` guard's two branches are `m` (`= 0`,
  literal) and the reduced inner term (`= n`) — two DIFFERENT terms, not one
  term repeated. The fix is a nested `cases_zero_succ` on `n` itself inside
  the `fuel = succ f` branch; once `n`'s shape is exposed, both leaves close
  by `refl`. This is `lorAux`'s fuel-exhaustion row (returns `n`, not `0`)
  biting, not its guard order. `declare_lor_aux_agree_of_fuel` itself,
  once `lor_aux_zero_left_any_fuel` existed, WAS close to the sizing — a
  guard/bit-combine swap, no new proof technique.
- **`ldiffAux`'s transport matched the sizing exactly.** Its
  `zero_left_any_fuel` is byte-for-byte `land`'s proof (same absorbing-zero
  base case, confirmed by tracing the reduction: at `m = 0` fixed, both the
  outer and inner guards ultimately collapse to the constant `0` via
  `bool_select_nat_same`, exactly as `land`'s does). Its `agree_of_fuel`
  step needed only the hybrid guard swap (`on_n_zero = m` pass-through like
  `lor`, `on_m_zero = 0` absorbing like `land`) and the `beq`-based per-bit
  combine — no new case split.

**Negative control per transport** (mandatory, insufficient-fuel, checked by
evaluation alone since no `Le m fuel` proof exists at the chosen witness):

Detail moved to [`../notes/239-nat-fuel-transport.md`](docs/plan/notes/239-nat-fuel-transport.md).

**Your lane's block (`DONE`, nat-singles, 2026-08-29).** Landed both
unassessed facts: `Nat.mod_lcm` and `Nat.dvd_of_forall_prime_mul_dvd`.
Neither needed the stated blockers to be investigated first -- nobody had
looked, and both turned out to have short proofs from infrastructure already
in the prelude (`Nat.lcm_dvd`, `crt.rs`'s `gap_dvd`/`modeq_of_dvd_gap`,
`Nat.exists_prime_dvd`).

`Nat.mod_lcm : modEq n x y -> modEq m x y -> modEq (lcm n m) x y`,
**unconditional** in `n`/`m` (unlike `Nat.crt_unique`, which needs
`gcd n m = 1`). The combination step is `Nat.lcm_dvd : dvd n c -> dvd m c ->
dvd (lcm n m) c`, already unconditional, so the whole proof is `crt_unique`'s
own `crt_le`/`gap_dvd`/`modeq_of_dvd_gap` shape with `lcm_dvd` swapped in for
`coprime_mul_dvd`. `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`, private) were
widened to `pub(super)` and reused from `lcm.rs` rather than duplicated.

`Nat.dvd_of_forall_prime_mul_dvd : (forall p, Prime p -> p|a -> p*a|b) ->
a|b`. Turned out to need only ONE prime dividing `a` (any one), not
induction over `a`'s factorization: `a=0` uses the hypothesis at `k=2`;
`a=1` needs `dvd_mul`+`one_mul` and never touches the hypothesis; `a>=2`
uses `exists_prime_dvd` for a witness `pw`, the hypothesis at `k=pw` gives
`pw*a | b`, and `a | (a*pw)` (`dvd_mul` + `mul_comm`) chains via `dvd_trans`.
Same nested `lt_or_ge`-on-`a` trichotomy as the neighbouring
`coprime_of_forall_prime_dvd`.

The other two facts (`F:ml430-nat-coprime-of-lt-minfac-0f79bdba`,
`F:ml430-nat-coprime-iff-isrelprime-0c08eb25`) are left `open`, confirmed
still blocked (re-grepped the whole `crates/axeyum-lean-kernel/src/` for
`minFac`/`min_fac` and `IsRelPrime`/`is_rel_prime`/`isRelPrime`: zero hits
outside this status doc and the fact files themselves) -- see "What's still
needed" below for the precise construction each one is missing.

`nat_prelude` count: **85 + 441 -> 85 + 443** (2 new theorems, 0 new
definitions; confirmed by `the_build_is_deterministic`'s own panic message,
not hand-counted).

## What's still needed for the other two facts

Detail moved to [`../notes/240-nat-singles.md`](docs/plan/notes/240-nat-singles.md).

**Your lane's block (`DONE`, nat-minfac-relprime, 2026-08-29).** Landed the
required fact and the bonus definition sized in
[`docs/plan/status/240-nat-singles.md`](docs/plan/status/240-nat-singles.md).

`Nat.IsRelPrime m n := ∀ d, d ∣ m → d ∣ n → d = 1` (`rel_prime.rs`), a genuine
new `Definition` — Mathlib's generic `∀ d, d∣x → d∣y → IsUnit d`
(`Mathlib/Algebra/Divisibility/Units.lean:150`) specialized to `Nat`'s only
unit, `1`. Both directions of `Nat.coprime_iff_isRelPrime` were exactly as
cheap as the handoff predicted: forward combines `d∣m`/`d∣n` via `dvd_gcd`,
transports along the hypothesis to `d∣1`, and closes with
`eq_one_of_dvd_one`; backward applies the hypothesis directly at
`d := gcd m n`, discharged by `gcd_dvd_left`/`gcd_dvd_right`. No case
analysis in either direction, and neither unfolds `Nat.gcd`'s own recursion.
Closes `F:ml430-nat-coprime-iff-isrelprime-0c08eb25` (flipped `open` ->
`proved`; the mirror flip is honest — verified by reading Mathlib's actual
source for `IsRelPrime` at the pinned commit, not inferring from the
theorem's statement).

**Bonus: `Nat.minFac`/`Nat.minFacAux` landed** (`min_fac.rs`), a fuel-recursive
linear divisor search — structural `Nat.rec` on a `fuel` argument (the same
device `Nat.div`/`Nat.mod`/`Nat.log` use), fuel `= n - 2`, scanning candidates
`2, 3, 4, …` via `beq (mod n candidate) 0`. Fuel exhaustion coincides exactly
with `candidate = n` (never earlier), so the base case "return the candidate
unchanged" is correct — `n` trivially divides itself. `minFac 0 = 2` and
`minFac 1 = 1` are an outer case split before the search runs, matching
Mathlib's boundary conventions.

Detail moved to [`../notes/241-nat-minfac-relprime.md`](docs/plan/notes/241-nat-minfac-relprime.md).

**Your lane's block (`DONE for this pass`, int-emod-negative, 2026-08-29).**
Landed **two of the three** lemmas `docs/plan/status/236-int-gcd-div-2.md`
named as the missing pieces for `F:ml430-int-gcd-div-5e01872f`
(`Int.gcd_div`): `Int.emod_natAbs_bound` (the keystone) and
`Int.ediv_emod_unique_general`. `Int.gcd_div` itself stays open, precisely
scoped below. No ledger edit was made — the fact is still `open`.

**Verified before starting**: no inline negative-divisor `emod` bound exists
anywhere in `wilson.rs`, `crt.rs`, or `modinv.rs` (grepped proof bodies, not
names, per the brief). `crt.rs`'s own module doc already states the gap
directly — "this development has no bound on emod's magnitude for a
negative modulus" — confirming the prior handoff's assessment rather than
finding a shortcut around it.

**1. `Int.emod_natAbs_bound`** (`int_prelude/division.rs`):
`∀ a b, Not (Eq Int b zero) → Int.lt (emod a b) (ofNat (natAbs b))`.
Every one of the four `Int.rec` branches reuses existing machinery rather
than re-deriving it: `natAbs` is an unconditional ι-reduction (`ofNat n ↦
n`, `negSucc n ↦ succ n`), so the divisor's magnitude collapses to exactly
the shapes `emod_lt_of_pos`'s two row builders (`row_emod_lt_of_pos_of`,
`row_emod_lt_of_pos_neg`) and the `sub_nat_nat_lt_ofnat` combinator already
handle — reused directly. The `b ≠ 0` hypothesis is load-bearing in exactly
one of the four branches (`ofNat m, ofNat n`, where `n` could be `0`),
derived via the contrapositive of `nat_eq_to_int` plus
`Nat.zero_lt_of_ne_zero` and the general `Nat.mod_lt : 0 < n → m % n < n`
(no `succ`-shape pinning needed, unlike `emod_lt_of_pos`, which cannot state
this bound for a negative divisor at all).

Detail moved to [`../notes/242-int-emod-negative.md`](docs/plan/notes/242-int-emod-negative.md).

**Your lane's block (`DONE`, nat-lor-comm, 2026-08-29).** `Nat.lor_comm`
landed and `F:ml430-nat-lor-comm-2666d7ef` is closed. This was the exact task
`docs/plan/status/239-nat-fuel-transport.md` sized as "the same treatment as
`land_comm`, transported to `lorAux`" — that sizing UNDERCOUNTED it, for a
reason worth stating precisely: `land_aux_comm_of_fuel` needs no hypothesis
at all, and its `lor` twin needs two.

**What the kernel rejected, and why: nothing.** `lor_aux_comm_of_fuel` and
`lor_comm` were both admitted on the FIRST `cargo test` run — no rejection to
diagnose, exactly as `land_comm`'s own construction reported.

**Why the sizing was wrong, precisely.** `land`'s fuel-exhaustion row is the
constant `0` regardless of argument order, so
`∀ fuel m n, Eq (landAux fuel m n) (landAux fuel n m)` is TRUE even at
insufficient fuel and needs no hypothesis. `lorAux`'s row is pass-through
(`lorAux 0 m n = n`), so the unconditional analogue is FALSE:
`lorAux 0 0 1 = 1` while `lorAux 0 1 0 = 0` (simulated in Python before
committing to this as the negative-control witness — copying `land`'s own
`(1, 7, 7)` witness would have been VACUOUS here, since `lorAux 1 7 7 = 7 =
lorAux 1 7 7` swapped, no disagreement at all). So
`Nat.lor_aux_comm_of_fuel : ∀ fuel m n, Le m fuel → Le n fuel → Eq (lorAux
fuel m n) (lorAux fuel n m)` carries hypotheses `land`'s analogue does not,
and BOTH matter:

- The base case (`fuel = 0`) needs both `Le m 0`/`Le n 0` to force `m = n =
  0` via `le_antisymm` + `zero_le` — without them the base statement is
  simply false.
- The both-nonzero step needs `half_le_predecessor_of_succ` bounds for BOTH
  halves (`half_a_le_k` AND `half_b_le_k`) to apply the induction hypothesis,
  because the IH itself carries the same two hypotheses. `land`'s analogous
  step needs neither bound at all — it applies its IH unconditionally.

**Which of the four `(m = 0?, n = 0?)` cases differed from `land`'s, as the
brief asked.** All four differed in SHAPE from land's (since `land`'s guard
returns a constant `0` under both guards and `lor`'s returns a pass-through
value), but only the base case and the both-nonzero case needed genuinely
different PROOF TECHNIQUE:

Detail moved to [`../notes/243-nat-lor-comm.md`](docs/plan/notes/243-nat-lor-comm.md).

**Your lane's block (`DONE (1 of 4 landed as a new local fact; 3 blocked from
an ml430 flip by verified reasons independent of proof difficulty)`,
nat-testbit-bitwise, 2026-08-29).**

Before writing any kernel code, verified (Step 0 of the brief) whether the
four assigned facts are actually closeable, and found a same-day blocker the
brief was not aware of: `docs/plan/status/235-nat-bitwise-facts.md` (a full
triage of all 19 `natural-bitwise` facts, landed earlier in this session)
already establishes that **none of the four facts this lane was assigned can
be honestly closed as pinned `ml430` mirrors**, for two independent reasons,
both re-verified directly against the current tree rather than trusted from
the doc:

1. **Genuine codomain mismatch.** Mathlib's `Nat.testBit (n i : Nat) : Bool`
   (confirmed at use sites — `testBit_land` states
   `testBit (m &&& n) k = (testBit m k && testBit n k)` using `Bool.&&`).
   Our `Nat.testBit` (`nat_prelude/binary.rs`, `testBitAux`) is
   `Nat -> Nat -> Nat`, returning `{0,1}` as a `Nat` (confirmed by reading
   `declare_test_bit_defs` and `test_bit_le_one` directly). This is not an
   alternate construction of the same type — closing a Bool-typed pinned
   `formal.statement` with a Nat-valued proof would be "manufacturing a
   flip" against CLAUDE.md's own honest-flip criterion.
2. **A live gate would break regardless of provability.**
   `scripts/gen-autogenesis-bitwise-family-projection.py` (invoked by
   `just autogenesis-bitwise-semantic-law-demand`, confirmed present in
   `justfile:667`, NOT part of `just check`'s dependency chain) hard-`raise`s
   if `F:ml430-nat-testbit-land-dfef7ca4` / `-lor-` / `-ldiff-`
   `epistemic_status != "open"`. This applies independently of (1) — even a
   fully honest Bool-valued proof would still break this named recipe.

`F:ml430-nat-zero-of-testbit-eq-false-e244c9a1` is not in that gate script's
mapping, but still has problem (1): its statement is
`(∀ i, n.testBit i = false) → n = 0`, Bool-valued.

Detail moved to [`../notes/244-nat-testbit-bitwise.md`](docs/plan/notes/244-nat-testbit-bitwise.md).

**Your lane's block (`DONE`, int-fib-two-mul, 2026-08-29).** Both targets
landed, kernel-checked and axiom-free, closing `F:ml430-int-fib-two-mul-0e70f3dd`
and `F:ml430-int-fib-two-mul-add-two-0ba4a948`.

- `Int.fib_two_mul : ∀ n, Eq Int (fib (mul two n)) (mul (fib n) (sub (mul two
  (fib (add n one))) (fib n)))`.
- `Int.fib_two_mul_add_two : ∀ n, Eq Int (fib (add (mul two n) two)) (mul
  (fib (add n one)) (add (mul two (fib n)) (fib (add n one))))`.

`int_prelude::` went **46 → 48 passing** (44 → 46 before the two new
concrete-instantiation negative-control tests were added), `derived_laws`
156 → 158 (recounted by grep, not incremented), integer trusted surface
still 0. No induction was needed for either theorem — both are direct
algebra from `Int.fib_add` (already proved) and `Int.fib_rec`.

**The prior lane's sizing was accurate on the algebra and silent on the
actual cost.** "~200–250 lines each, no new device" held for the algebra
itself, and no genuinely new proof DEVICE was needed (everything routes
through `mul_comm`, `left_distrib`, `Int.mul_sub`, `add_assoc`/`add_comm`,
`Int.fib_add`, `Int.fib_rec`). What the sizing didn't — and couldn't —
predict was a mechanical bug that cost most of this lane's time.

## The subtraction bridge

Built first, as the brief asked, before either theorem:

```
/// h : Eq Int (add a b) c  |-  Eq Int b (sub c a)
fn eq_sub_of_add_eq_left(d, a, b, c, h) -> ExprId
```

From `a + b = c` derive `b = c - a`. Route: commute `a+b` to `b+a` (so `h`
reads `b+a = c` after a `trans`), then `Int.add_neg_cancel_right b a :
(b+a)+(-a) = b`; substituting `c` for `b+a` gives `c+(-a) = b` (== `sub c a
= b` after folding `Int.sub`); flip. It is reusable and IS reused —
`fib_pred_eq_sub` (below) is its only consumer so far, but the shape (turn
a recurrence equation into a subtraction) is generic and not tied to
Fibonacci at all.

Detail moved to [`../notes/245-int-fib-two-mul.md`](docs/plan/notes/245-int-fib-two-mul.md).

**Your lane's block (`DONE for this pass`, int-gcd-div, 2026-08-29).**
`F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) is **CLOSED** — `proved`,
axiom-free, statement identical to Mathlib's. Built the fourth bridge lemma
the `int-emod-negative` lane's handoff (`docs/plan/status/242-int-emod-negative.md`)
named but did not build, then `Int.gcd_div` itself, for a divisor of **any
sign or zero** — Mathlib's own hypotheses (`c ∣ a`, `c ∣ b`) carry no
restriction on `c`, and this proof does not add one.

**Verified the mirror-flip criterion myself, against the pinned Lean 4
source, before writing any proof.** Mathlib v4.30's `Int.gcd_div` is
`alias gcd_div := gcd_ediv` (`Mathlib/Data/Int/GCD.lean`); `Int.gcd_ediv`
itself is not restated in Mathlib at all — it lives in Lean 4 core
(`Init/Data/Int/Gcd.lean`, read at the pinned toolchain commit under
`/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/`),
stated over `/`. Core's own `instance : Div Int` (`Init/Data/Int/DivMod/Basic.lean`)
binds `/` to `Int.ediv`, with the comment "for compatibility with SMT-LIB" —
the SAME Euclidean division this development's `Int.ediv` already matches
bit for bit (confirmed by reading `Int.ediv`'s Lean 4 core recursive
definition and this repo's `int_prelude/division.rs` module doc side by
side). So this is a genuine same-definition mirror (honest flip per
CLAUDE.md's criterion), not a restatement of a different proposition — and
critically, since neither Mathlib's alias nor core's `gcd_ediv` carries a
`c ≠ 0` hypothesis, the fully general (`c` any sign, `c = 0` included)
statement is what had to be proved, not a restricted one.

Detail moved to [`../notes/246-int-gcd-div.md`](docs/plan/notes/246-int-gcd-div.md).

**Your lane's block (`OPEN`, nat-bitwise-assoc, 2026-08-29).** Neither
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) nor
`F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) closed this session. What
landed instead is a real, tested, reusable piece of the infrastructure the
brief named as needed — `Nat.land_aux_le_left`/`Nat.land_le_left` — plus a
precise diagnosis of why the natural next step (a fuel-parametrized
`land_aux_assoc_of_fuel`, mirrored on `land_aux_comm_of_fuel`) does not go
through the way commutativity did, and what it would actually take.

**What landed and is kernel-checked.**

- `Nat.land_aux_le_left : ∀ fuel m n, Le (landAux fuel m n) m` — `landAux`
  never exceeds its LEFT operand, at ANY fuel, sufficient or not. This is
  exactly the bound the brief flagged: *"a nested `landAux fuel a b` in the
  fuel-recursion's ARGUMENT position is not obviously bounded by fuel, so
  the re-fuelling step may need a lemma saying `landAux fuel a b ≤ a`
  ... before the outer application's fuel is known sufficient."* No such
  lemma existed; this is it.
- `Nat.land_le_left : ∀ a b, Le (land a b) a` — the one-line `land`-headed
  corollary at `fuel := m := a` (defeq to `land a b`, no extra proof step,
  same shape as `land_aux_eq_land_of_le`'s corollary).

Both proved by ordinary induction on `fuel` alone
(`agree_by_fuel_induction`, no sufficient-fuel hypothesis needed at all,
unlike fuel-irrelevance): the `m = 0` and `n = 0` leaves close via
`land_aux_zero_left_any_fuel` and the literal-`n = 0` guard trick already
used throughout `rec_agreement.rs`; the "both positive" leaf bounds
`2*rec + bit` by `2*(m/2) + (m%2) = m` via `mul_le_mul_left`,
`add_le_add_left`/`add_le_add_right`, `le_trans`, and the executable
div/mod identity (`div_mod_exec`, extracted with `helpers::and_left`
following `division.rs`/`group.rs`'s `div_mod_unique` pattern — a NEW
private helper `bit_product_le_left` bounds `(m%2)*(n%2) ≤ m%2` via
`n%2 ≤ 1` monotonicity, since `mod_lt` + `le_of_lt_succ` give `n%2 ≤ 1`
directly and this route needed no `cases_mod_two` case split at all).

Detail moved to [`../notes/247-nat-bitwise-assoc.md`](docs/plan/notes/247-nat-bitwise-assoc.md).

**Your lane's block (`DONE for this pass`, pin-recount-shapes, 2026-08-29).**
`scripts/recount-pinned-inventory.py` recognized exactly one array shape and
answered "no pinned inventory array found" for the site whose merge it was run
against. Its counting engine is now shape-independent, verified against every
pinned array in the tree, and carries six new mutation-verified controls. The
survey below **re-measures**
[`docs/research/11-design-review/2026-08-29-the-pin-recount-tool-covers-one-of-four-shapes.md`](docs/research/11-design-review/2026-08-29-the-pin-recount-tool-covers-one-of-four-shapes.md)
and corrects it in four places.

Commits: `ce173137b` (engine), `ed8335521` (controls), plus this file.

## What landed

**One engine, not four regexes.** The line-shape heuristic (`^        \("` /
`^        \($`) is gone. The tool now masks comments, string literals and char
literals, then splits each array literal on **top-level commas** with a
bracket-depth counter. That covers `[(&str, crate::NameId, &str); N]`,
`[crate::NameId; N]`, `[&str; N]`, `let`/`const`/`static` and function-return
positions, and multiple pinned arrays per file.

Masking is load-bearing twice, not cleanup. This repository's doc comments carry
deliberately unbalanced brackets (`[0,n)`, intra-doc links) that wreck a depth
counter; and `creal/inventory.rs`'s module docs **quote a pin declaration in
prose** to explain why that pin is gone, which an unmasked scan matches and then
fails on as "not terminated by `];`". The old control suite worked around that
with an anchored grep and noted the anchor "is also the right fix for the tool" —
masking is that fix and is strictly stronger (an anchored scan still matches an
indented `//!` code block).

**Verified, both directions.** All 72 pinned-array sites in the tree report
`declared == counted`, which agrees with the compiler (the tree builds, so every
pin is correct by construction) — so a tool that were wrong about any real shape
would show a false `PIN WRONG` here. That is not a vacuous pass: the pre-existing
`a_wrong_pin_exits_nonzero` control pins that the tool can say `PIN WRONG` at
all, and `every_wrong_pin_in_one_file_is_rewritten` pins that it rewrites the
right pin when a file has several.

**One diagnostic bug found and fixed.** `single`/`wrapped` were measured on the
source, so an entry preceded by a `//` block read as *wrapped*.
`int_prelude_tests.rs`'s `derived_lemmas` reported `wrapped=1` with nothing
wrapped in it. `wrapped` names the measured 210-vs-283 failure, so it must not
also fire for a comment; it is now measured on the masked text.

## Deliverable 1 — the re-measured survey

Detail moved to [`../notes/248-pin-recount-shapes.md`](docs/plan/notes/248-pin-recount-shapes.md).

Status: **DONE.** Seven declarations landed in a new
`crates/axeyum-lean-kernel/src/creal/ivt_boundary.rs`, all accepted by
`Kernel::add_declaration` on the **first** attempt, all axiom footprint 0. One
curated fact registered. Nothing in `creal/ivt.rs` was touched.

## Step 0 — the gap was real

`grep -n 'name_str(creal, "ivt' crates/axeyum-lean-kernel/src/creal.rs` returned
the fifteen existing `ivt_*` names and **no** row-2 declaration; the only
`decides`-shaped name anywhere in the crate was
`evt_attained_max_decides_sign`. The brief's reading was correct and the note
that produced it (`docs/research/11-design-review/2026-08-29-ivt-has-no-row-2-theorem-evt-does.md`)
was not stale.

## What was proved

```text
CReal.ivt_exact_root_decides_sign :
  ∀ v c, le zero c → le c one →
    Equiv (min c (max (add c (neg one)) v)) zero →
    Or (le v zero) (le zero v)
```

Verbatim from `kernel_declaration_projection`:

```text
((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le CReal.zero x1) ->
  ((x3 : CReal.le x1 CReal.one) -> ((x4 : CReal.Equiv (CReal.min x1
  (CReal.max (CReal.add x1 (CReal.neg CReal.one)) x0)) CReal.zero) ->
  Or (CReal.le x0 CReal.zero) (CReal.le CReal.zero x0))))))
```

The full statement family, seven declarations, `creal` prelude, footprint 0
each:

Detail moved to [`../notes/249-ivt-row-two.md`](docs/plan/notes/249-ivt-row-two.md).

**Your lane's block (`DONE`, nat-fastfib-minfac, 2026-08-29).** Two
independent ml430 facts, briefed together. One closes with real new content
under its own name (not a flip); the other is sized and left open with a
precise reason, per the brief's explicit "one of two is a good outcome"
bar — but the one that closed does the harder of the two proof arguments the
prior lane (`docs/plan/status/241-nat-minfac-relprime.md`) sketched and left
undone.

## `F:ml430-nat-coprime-of-lt-minfac-0f79bdba` — closed via a NEW fact, not a flip

`docs/plan/status/241-nat-minfac-relprime.md` already established (reading
Mathlib's actual source, not inferring) that this mirror must stay `open`:
Mathlib's `Nat.minFac` is well-founded recursion on a `sqrt n`-bounded
measure that skips even candidates and exits early once `k*k > n`; this
repository's `Nat.minFac` (`min_fac.rs`) is fuel-STRUCTURAL recursion
scanning every candidate `2, 3, 4, …` with no skip and no early exit. Same
value at every `n`, different construction — the `Nat.multichoose` case in
CLAUDE.md's mirror-flip criterion, not `Nat.descFactorial_of_lt`'s. That
lane's own handoff sketched exactly the two pieces still needed and sized
them as "further, separate work." This lane built both:

Detail moved to [`../notes/250-nat-fastfib-minfac.md`](docs/plan/notes/250-nat-fastfib-minfac.md).

**Your lane's block (`DONE`, nat-bit-decode, 2026-08-29).** `Nat.land_bit`
is landed (`F:ml430-nat-land-bit-b9ab7475` flipped open → proved), plus the
reusable `Nat.bit` decode bridge two prior lanes
(`docs/plan/status/237-nat-fuel-irrelevance.md`,
`docs/plan/status/239-nat-fuel-transport.md`) each independently named as
the blocker and did not attempt. `Nat.lor_bit`/`Nat.ldiff_bit` remain open
— see "What is still needed" below for a precise diagnosis of what each
needs beyond this lane's work.

**The construction, in `crates/axeyum-lean-kernel/src/nat_prelude/bit_decode.rs`
(new file, per the brief — did not touch `land.rs`/`lor.rs`/`ldiff.rs`/
`rec_agreement.rs`).** `land m n := landAux m m n` uses `m` itself as fuel,
and `bit a m` is not syntactically `zero`/`succ`-shaped for symbolic `a`,
`m` (`add (mul 2 m) (cond a 1 0)`, stuck), so the canonical fuel cannot be
unfolded by one `Nat.rec` step. The fix swaps the fuel via
`Nat.land_aux_eq_land_of_le` for an artificially chosen `succ`-shaped one
(`base := mul 2 m`, `k1 := succ base = bit true m`, `fuel := succ k1`),
both bounds (`Le (bit a m) fuel`, `Le m k1`) holding unconditionally
(`a = true` makes `bit a m` DEFEQ `k1` exactly; `m ≤ mul 2 m ≤ k1` via
`two_mul_eq_add_self` + `le_add_right` + `le_succ`). One `Nat.rec` step
then unfolds to the shared `guarded` combinator (reproduced locally rather
than made `pub(super)` in `rec_agreement.rs`, to avoid a cross-lane edit to
that file) at the raw `div`/`mod` subterms, decoded back to `(m, n)` by two
new lemmas — `Nat.bit_div_two`, `Nat.bit_mod_two`, each one
`div_mod_unique` call against `Nat.div_mod_exec` (the reconstruction
equation is `bit`'s own definition, closed by `refl`; the bound
`cond test 1 0 < 2` is a two-leaf `Bool` split) — after which the recursive
occurrence swaps back to canonical `land m n` via `land_aux_eq_land_of_le`
again.

Detail moved to [`../notes/251-nat-bit-decode.md`](docs/plan/notes/251-nat-bit-decode.md).

**Your lane's block (`OPEN`, nat-assoc-dichotomy, 2026-08-29).** Neither
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) nor
`F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) closed this session —
this is the third lane to stop at this wall. What landed: the missing
arithmetic item `docs/plan/status/247-nat-bitwise-assoc.md` named
(`Nat.add_eq_zero`) plus a second piece its own diagnosis needed but did
not name (`Nat.zero_or_succ`), both kernel-checked, tested, and
registered — and, more valuably, a **fully worked, numerically-verified
proof plan** for `land_aux_assoc_of_fuel` that goes well past the prior
diagnosis: it identifies the exact case tree, shows 6 of 8 base leaves
close by pure computation with **no new lemma at all**, and shows the
remaining hard leaf needs one more substantial theorem (not yet built)
whose own proof I traced through completely by hand and cross-checked in
Python.

**Why the actual `land_aux_assoc_of_fuel`/propagation-lemma code is NOT in
this commit, even though I have a verified plan for it:** both belong in
`rec_agreement.rs` (where their siblings `land_aux_comm_of_fuel`,
`land_aux_le_left` already live), and the brief that opened this lane
explicitly named `rec_agreement.rs`, `land.rs`, `lor.rs`, `ldiff.rs`,
`binary.rs` as files sibling lanes are in RIGHT NOW. Writing a
~300-400 line addition into a file under active concurrent edit is exactly
the shared-file collision this repository's multi-agent hygiene section
warns about, so I did not. Everything below is written so the next lane
into `rec_agreement.rs` can implement it directly without re-deriving any
of it.

## What landed and is kernel-checked

Detail moved to [`../notes/252-nat-assoc-dichotomy.md`](docs/plan/notes/252-nat-assoc-dichotomy.md).

**Your lane's block (`DONE (Nat.xor landed; both assigned facts stay open,
reasons recorded)`, nat-xor-parity, 2026-08-29).**

## Step 0: does `Nat.xor` exist?

No — confirmed by grep (`bitwise.rs`'s own module doc says so explicitly:
"no prelude XOR sibling exists") and by the absence of any `mod xor;` under
`nat_prelude/`. No theorem-inventory tool was needed since the negative was
already explicit in source comments, not just an absent grep hit.

## What landed: `Nat.xor := Nat.bitwise xor_fn`

The "alternative worth checking first" the brief named was the right call.
`bitwise.rs` already carries the general `Nat.bitwise f m n` combinator
(landed by an earlier lane, `declare_bitwise_all`), already builds
`xor_fn` (`Bool.xor`, `pub(super)`) purely to instantiate `f` for its own
`bitwise_xor_three_five` sanity check, and that check already proves
`Eq (bitwise xor_fn 3 5) 6`. So `Nat.xor` did not need a fourth hand-rolled
`bitwiseAux`-shaped fuel recursion — it is a direct partial application:

```
Nat.xor := Nat.bitwise xor_fn      -- Nat -> Nat -> Nat
```

This is the SAME shape Mathlib v4.30 uses (`Mathlib.Data.Nat.Bitwise`:
`Nat.xor := bitwise xor`), not merely something pointwise-equal to it. The
absorbing-zero question the brief flagged (does the fuel operand carry the
operator's absorbing zero?) turned out to be moot for this definition: `xor`
inherits `bitwise`'s own general, `f`-independent boundary theorems
(`bitwise_zero_left`/`bitwise_zero_right`) rather than needing new
hand-written base-case rows. For the record (checked anyway, since the rule
is worth confirming even when not load-bearing): XOR is `lor`-shaped
(`0 xor n = n`), and `bitwise_aux`'s general fuel-exhaustion row
(`if f false true then n else 0`) reproduces exactly that at `f = xor_fn` by
δβι alone (`xor false true` reduces to `true`, so the row returns `n`) —
consistent with `bitwise.rs`'s own derivation for `lor`.

Detail moved to [`../notes/253-nat-xor-parity.md`](docs/plan/notes/253-nat-xor-parity.md).

**Your lane's block (`DONE (bridge landed; Nat.even_xor landed and closes
F:ml430-nat-even-xor-78a39432; Nat.lt_xor_cases stays open)`,
nat-parity-lowbit, 2026-08-29).**

## What landed

### 1. The bridge: `Nat.even_iff_mod_two_eq_zero` / `Nat.odd_iff_mod_two_eq_one`

`nat_prelude/parity.rs`:

```
Nat.even_iff_mod_two_eq_zero : ∀ n, Iff (Even n) (Eq (mod n 2) 0)
Nat.odd_iff_mod_two_eq_one   : ∀ n, Iff (Odd n)  (Eq (mod n 2) 1)
```

Neither half of this existed anywhere in the prelude, inline or otherwise
(checked: `parity.rs`'s own module doc said so, and `binary.rs`'s seven
`mod _ 2` sites use `Lt r 2` only as a bound, never split). Built fresh,
not extracted:

- `mp` (`Even n -> Eq (mod n 2) 0`): eliminate the existential
  (`Exists.rec`, the same shape `declare_even_not_odd` already uses) to
  `k, hk : Eq n (add k k)`, then a `d.chain` rewriting `mod n 2` through
  `hk`, a new `mul_two_eq_add_self` conversion (`k+k` <-> `mul two k`, via
  `succ_mul`/`one_mul` — the exact inline technique `binary.rs`'s
  `n_lt_mul_two` already uses for a `Lt` conclusion, extracted here as a
  standalone equality), an `add_zero` insertion, and a new
  `mod_two_mul_add_of_lt` helper closing the last step.
- `mpr` (`Eq (mod n 2) 0 -> Even n`): `div_mod_exec` gives
  `n = add (mul two (div n 2)) (mod n 2)`; substitute the hypothesis,
  simplify, convert to `add`-form via `mul_two_eq_add_self`, hand the
  result to `Exists.intro` at witness `div n 2`.
- The `Odd` twin needs one more piece, `succ_eq_add_one`
  (`Eq (succ a) (add a one)`, via `add_succ`/`add_zero` reversed) to
  bridge `succ(k+k)` and `add (mul two k) 1`.

Detail moved to [`../notes/254-nat-parity-lowbit.md`](docs/plan/notes/254-nat-parity-lowbit.md).

**Your lane's block (`DONE`, nat-binaryrec, 2026-08-29).** Both pieces of
infrastructure `docs/plan/status/250-nat-fastfib-minfac.md` named as blocking
`Nat.fastFib` are landed and kernel-checked: a **product type** and a
**bit-halving recursion combinator**, plus the recursive equation that makes
the combinator usable in a proof rather than only in a computation.
`Nat.fastFib` itself was **not** built — see "Where I stopped".

The honesty question the brief asked is answered against Mathlib's actual
source, and the answer changes what a future `fastFib` lane should aim at:
**a fuel encoding is a different construction, so `F:ml430-nat-fastfib-eq-cde11774`
stays `open` even after `fastFib` is built.**

New declarations: 4 definitions + 14 theorems + 1 inductive family (3 names).
`nat_prelude::` sweep **133 passed, 0 failed** (was 132). `nat` trusted
surface unchanged at **0**.

## 1. Was a pair type already available? No — and here is how I determined it

`Prod` appears in four files, and **none of them is a prelude declaration**:

| site | what it is |
| --- | --- |
| `inductive/inductive_tests.rs:1399` | a **test fixture** — `prod_two_params_one_ctor` admits `Prod α β` through `add_inductive` and checks its recursor's iota rule. Never built into any prelude. |
| `inductive.rs:23`, `env.rs:122` | module-doc prose naming `Prod` as a shape the inductive layer supports |
| `creal.rs:4042`, `creal/ivt.rs:2324` | doc comments explaining a deliberate choice NOT to introduce one |
| `nat_prelude/diagonal.rs:39`, `int_prelude/bezout_witnesses.rs:55` | doc comments recording the same absence |

Detail moved to [`../notes/255-nat-binaryrec.md`](docs/plan/notes/255-nat-binaryrec.md).

Status: `bitwise_comm` LANDED and closed. `lt_xor_cases` NOT attempted --
sized only (see below), per the brief's "landing bitwise_comm alone is a
good outcome."

## Task
- `F:ml430-nat-bitwise-comm-1a273bae` (`Nat.bitwise_comm`) -- primary
  target. **DONE**, flipped to `proved`.
- `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`) -- secondary.
  **NOT attempted.** Still `open`.

## `bitwise_comm`: what was built and why

### Did the unconditional form hold, or did it need `Le` hypotheses?

Needed `Le` hypotheses -- `lor`'s shape, not `land`'s. A Python simulation
(`bitwiseAux` re-implemented directly, not committed -- pure scratchpad)
run BEFORE any Rust was written:

```python
def bitwiseAux(f, fuel, m, n):
    if fuel == 0:
        return n if f(False, True) else 0
    if n == 0:
        return m if f(True, False) else 0
    if m == 0:
        return n if f(False, True) else 0
    return 2 * bitwiseAux(f, fuel - 1, m // 2, n // 2) + \
        (1 if f(m % 2 == 1, n % 2 == 1) else 0)
```

Result: `bitwiseAux(or, 0, 0, 1) = 1` but `bitwiseAux(or, 0, 1, 0) = 0` --
the unconditional (fuel not necessarily sufficient) form is FALSE whenever
`f false true = true` (`f = or`, `f = xor`), and true only when
`f false true = false` (`f = and`, matching `land`'s absorbing-zero row --
see CLAUDE.md's own "AND IT PROPAGATES INTO THE STATEMENT" entry, added
independently the same day and describing exactly this). With `Le m fuel`
AND `Le n fuel` (sufficient fuel for both operands), the statement held for
`and`/`or`/`xor` over 2000 random trials each, and `bitwise f m n =
bitwise f n m` (canonical fuel) held for all three over the full `0..60`
grid. So `bitwise_aux_comm_of_fuel` needed `lor`'s shape
(`Le m fuel -> Le n fuel -> ...`), generalized over `f`, plus an explicit
`hf : forall a b, f a b = f b a` hypothesis `land`/`lor` never needed
(their `f` is fixed and concrete, so commutativity is a closed fact, not a
hypothesis to thread).

### How `f`'s commutativity threads through the per-bit step (and where else it's needed)

Two sites need `hf`, not one:

Detail moved to [`../notes/256-nat-bitwise-comm.md`](docs/plan/notes/256-nat-bitwise-comm.md).

**Your lane's block (`OPEN`, nat-land-assoc-impl, 2026-08-29).** This lane
executed `docs/plan/status/252-nat-assoc-dichotomy.md`'s traced-but-unbuilt
theorem, verified the plan's own case tree against the actual guard
argument order and helper signatures, and landed it with tests. Neither
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) nor
`F:ml430-nat-lor-assoc-82c4d0fd` (`Nat.lor_assoc`) closed this session --
this is the fourth lane to stop short of `land_assoc` itself, but the
first to leave `land_aux_assoc_of_fuel` (the theorem that actually blocks
it) with a complete, line-by-line, implementation-ready derivation rather
than a sketch.

## What landed and is kernel-checked

**`Nat.land_aux_eq_zero_of_left_eq_zero : ∀ fuel a b c,
Eq (landAux fuel a b) 0 → Eq (landAux fuel a (landAux fuel b c)) 0`**
(`rec_agreement.rs`), exactly the statement `252` traced. Built via
`agree_by_double_fuel_induction` (its "two independently chosen fuels"
design reused here for three plain value arguments plus one fuel --
nothing in that helper actually requires the third generalized argument
to BE a second fuel, only that it be universally quantified alongside the
induction variable, which is exactly what this statement needs).

**Every step of `252`'s plan held, verified by compiling and running it,
not by re-reading the prose:**

Detail moved to [`../notes/257-nat-land-assoc-impl.md`](docs/plan/notes/257-nat-land-assoc-impl.md).

**Your lane's block (`DONE`, nat-lor-ldiff-bit, 2026-08-29).** `Nat.lor_bit`
(`F:ml430-nat-lor-bit-a2f98c7c`) and `Nat.ldiff_bit`
(`F:ml430-nat-ldiff-bit-6be49bb8`) are both landed, closing the trio
`docs/plan/status/251-nat-bit-decode.md` opened with `Nat.land_bit` and left
open for a follow-up lane. All three `Nat.bit`-decode facts are now `proved`.

**What transported unchanged from `nat-bit-decode`'s construction**
(`nat_prelude/bit_decode.rs`, new functions appended, `land.rs`/`lor.rs`/
`ldiff.rs`/`rec_agreement.rs`/`bitwise.rs` untouched): the fuel-swap machinery
(`base := mul 2 m`, `k1 := succ base`, `fuel := succ k1`, both `Le` bounds,
the `Nat.bit_div_two`/`Nat.bit_mod_two` decode via `div_mod_unique`) is
byte-for-byte the same shape for all three operators — it never inspects an
operator's absorbing-zero behaviour, only `Nat.bit`'s own encoding.

**What was new per operator (the actual task):**

Detail moved to [`../notes/258-nat-lor-ldiff-bit.md`](docs/plan/notes/258-nat-lor-ldiff-bit.md).

Status: `bitwise_swap` LANDED and closed. `bitwise_bit'` NOT attempted --
sized only in this file's earlier plan section, per the brief's "landing
one of the two is a good outcome."

## Task
- `F:ml430-nat-bitwise-swap-7175e90e` (`Nat.bitwise_swap`) -- primary
  target. **DONE**, flipped to `proved`.
- `F:ml430-nat-bitwise-bit-4c4b28a8` (`Nat.bitwise_bit'`) -- secondary.
  **NOT attempted.** Still `open`.

## `bitwise_swap`: what was built and why

### Simpler than `bitwise_comm`, and why

`bitwise_swap` states (pointwise, no `funext`): `forall f m n, Eq (bitwise
(swap f) m n) (bitwise f n m)` where `swap f := fun a b => f b a`. Unlike
`bitwise_comm`, it needs **no hypothesis on `f` at all**: `swap f` applied
to any two `Bool`s beta-reduces DIRECTLY to `f` applied to them in the
other order, because the swap is baked into which function gets applied
rather than asserted about a fixed one. Every site `bitwise_comm` needed
`hf : forall a b, f a b = f b a` plus `congr_bool_to_nat` for (the two
boundary rows and the per-bit combine) becomes pure defeq here.

Confirmed by hand-substitution (not Python -- the recursion is small enough
to trace directly by expanding `bitwiseAux (swap f) fuel m n` and
`bitwiseAux f fuel n m` case-by-case) BEFORE writing any Rust: every row
matches by beta/iota alone except the both-nonzero recursive step, which
needs exactly the induction hypothesis. Even there, the per-bit "bit" term
matches the other side EXACTLY (same term, after the beta-swap), so only
the recursive sub-call needs a `d.congr` -- no `bit`-side congruence at
all, unlike `bitwise_comm`'s `bitwise_bit_comm`.

### The two lemmas landed (`nat_prelude/bitwise.rs`, uncontended)

Detail moved to [`../notes/259-nat-bitwise-bit-swap.md`](docs/plan/notes/259-nat-bitwise-bit-swap.md).

**Your lane's block (`DONE (Nat.xor_comm landed; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, precise diagnosis recorded)`, nat-lt-xor-cases, 2026-08-29).**

## The exact Mathlib statement

Read directly from the pinned checkout
(`/data0/axeyum/lean-import-toolchain/mathlib4`, confirmed at commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, matching the fact's own
`prior_art.where`), `Mathlib/Data/Nat/Bitwise.lean:296`:

```lean
theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c
```

Matches `artifacts/facts/F-ml430-nat-lt-xor-cases-c43a1e85.json`'s
`formal.statement` verbatim (`∀ {a b c : ℕ}, a < b ^^^ c → a ^^^ c < b ∨ a
^^^ b < c`).

## Codomain check: does NOT block a flip

Six sibling `testBit`-family mirrors turned out unflippable because
Mathlib's `testBit` returns `Bool` against our `Nat`-valued `testBit`. This
statement mentions no `testBit` at all — every quantifier is `Nat`, every
operator (`<`, `^^^`, `∨`) already exists with a matching codomain in this
prelude, and `Nat.xor` is already the same `bitwise xor` shape Mathlib
uses. **An honest flip is possible once proved.** It is not proved here.

## What landed: `Nat.xor_comm`

New file `crates/axeyum-lean-kernel/src/nat_prelude/xor_order.rs`:

```
Nat.xor_comm : ∀ m n, Eq (xor m n) (xor n m)
```

Detail moved to [`../notes/260-nat-lt-xor-cases.md`](docs/plan/notes/260-nat-lt-xor-cases.md).

**Your lane's block (`DONE`, nat-land-assoc-finish, 2026-08-29).** Closed
`F:ml430-nat-land-assoc-ad4775b8` (`Nat.land_assoc`) by executing the
fully-traced derivation in `docs/plan/status/257-nat-land-assoc-impl.md` —
the fifth lane to work this target and the first to finish it. Every
traced step held as written; the one thing verified rather than trusted
was `257`'s own corrected leaf-split order (`c`, then `b`, then `a`),
re-confirmed against `guarded`'s actual `n`-outermost guard before
transcribing a single line.

## What landed and is kernel-checked

**`Nat.land_aux_assoc_of_fuel : ∀ fuel a b c, Eq (landAux fuel (landAux
fuel a b) c) (landAux fuel a (landAux fuel b c))`** (`rec_agreement.rs`),
unconditional (no `Le` hypothesis — `landAux`'s fuel-exhaustion row is
the absorbing constant `0`). Built via `agree_by_double_fuel_induction`,
step case split `c`, then `b`, then `a`:

Detail moved to [`../notes/261-nat-land-assoc-finish.md`](docs/plan/notes/261-nat-land-assoc-finish.md).

**Status: `DONE`.** `Nat.bitwise_bit'` (`F:ml430-nat-bitwise-bit-4c4b28a8`) is
landed, closing the last open member of the `Nat.bit`-decode `*_bit` family.
All four (`land_bit`, `lor_bit`, `ldiff_bit`, `bitwise_bit'`) are now `proved`.

## Task

- `F:ml430-nat-bitwise-bit-4c4b28a8` (`Nat.bitwise_bit'`) -- primary and only
  target, scoped by `docs/plan/status/259-nat-bitwise-bit-swap.md`. **DONE**,
  flipped to `proved`.

## What was built, in `nat_prelude/bitwise.rs` (uncontended at landing time)

The statement: `∀ f (a : Bool) (m : Nat) (b : Bool) (n : Nat), (m = 0 -> a =
true) -> (n = 0 -> b = true) -> bitwise f (bit a m) (bit b n) = bit (f a b)
(bitwise f m n)`.

**The fuel-swap machinery transports unchanged from `bit_decode.rs`'s
`land_bit`**, exactly as `docs/plan/status/259`'s sizing note predicted: an
artificially `succ`-shaped fuel (`base := mul 2 m`, `k1 := succ base`, `fuel
:= succ k1`), both `Le` bounds unconditional in `a`/`b`, then a `refl`-unfold
to the shared `guarded` step. `bitwise_aux_agree_of_fuel` (already declared
inside `declare_bitwise_comm`, general over ANY `f` -- no commutativity
needed) does BOTH fuel-swap steps directly, simpler than `land_bit`'s own
`land_aux_eq_land_of_le` two-step (no `symm` needed anywhere in the chain).

**Two things are new, both specific to a symbolic `f`, and both sized
correctly by `docs/plan/status/251`'s and `259`'s own diagnoses:**

Detail moved to [`../notes/262-nat-bitwise-bit-prime.md`](docs/plan/notes/262-nat-bitwise-bit-prime.md).

**Your lane's block (`DONE (Nat.testBit_xor landed, axiom-free; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, 3 pieces remain)`, nat-testbit-xor, 2026-08-29).**

## What landed

New file `crates/axeyum-lean-kernel/src/nat_prelude/testbit_bitwise.rs`:

```
Nat.testBit_xor : ∀ m n i,
  Eq (testBit (xor m n) i) (xor_bit (testBit m i) (testBit n i))
```

where `xor_bit(x, y) := bool_select_nat (xor_fn (beq x 1) (beq y 1)) 1 0` —
the same per-bit combine `bitwiseAux`'s own `succ_minor` row builds at bit
0 (`bitwise.rs`), generalized here to an arbitrary bit position.

This is piece (1) of the 4 pieces `docs/plan/status/260-nat-lt-xor-cases.md`
named as blocking `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`).
Admitted by the trusted kernel gate on the first attempt — no failed
`add_declaration` calls, no bisecting.

## Codomain check: local fact, not an `ml430` mirror

Mathlib's `testBit` returns `Bool`; this kernel's returns `Nat` in `{0,1}`
(`nat_prelude/binary.rs`'s module doc) — the same codomain mismatch that
made six sibling `testBit`-family mirrors unflippable (per the
`260-nat-lt-xor-cases.md` handoff and `F:nat-zero-of-testbit-eq-zero`'s own
note). No `ml430` fact for this exact statement was found in the ledger.
Landed as a new local fact, `F:nat-testbit-xor`
(`artifacts/facts/F-nat-testbit-xor.json`), `epistemic_status: proved`,
`axiom_footprint: []`, three independently-checked evidence rows (kernel
presence, concrete+symbolic compute, whole-prelude axiom-freedom).

## Keeping the two recursions in step

Detail moved to [`../notes/263-nat-testbit-xor.md`](docs/plan/notes/263-nat-testbit-xor.md).

**Your lane's block (`DONE (Nat.eq_of_testBit_eq + Nat.xor_assoc landed; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, 2 pieces remain with an exact route)`, nat-xor-algebra, 2026-08-29).**

## What landed

Piece 4 of the 4 pieces `docs/plan/status/260-nat-lt-xor-cases.md` named as
blocking `F:ml430-nat-lt-xor-cases-c43a1e85` was itself four sub-targets
(Mathlib's `xor_trichotomy` proof composes `xor_assoc`,
`xor_xor_cancel_left`, `xor_xor_cancel_right`, `xor_ne_zero_iff`). This lane
lands **one of those four in full, plus the general infrastructure the other
three now need only a small amount more to close**:

New file `crates/axeyum-lean-kernel/src/nat_prelude/xor_algebra.rs`:

```
Nat.eq_of_testBit_eq : ∀ m n, (∀ i, Eq (testBit m i) (testBit n i)) → Eq m n
Nat.xor_assoc        : ∀ a b c, Eq (xor (xor a b) c) (xor a (xor b c))
```

Both admitted axiom-free, both with concrete-discriminating + symbolic
evaluation tests, both registered as new local facts (`F:nat-eq-of-testbit-eq`,
`F:nat-xor-assoc`; neither has an `ml430` mirror — see "Codomain / mirror
check" below).

Detail moved to [`../notes/264-nat-xor-algebra.md`](docs/plan/notes/264-nat-xor-algebra.md).

**Your lane's block (`PARTIAL (piece 3 landed as F:nat-lt-of-testbit; piece
2 open, precise diagnosis recorded)`, nat-msb-order, 2026-08-29).**

## What landed

1. `Nat.self_lt_two_pow : forall n, Lt n (pow 2 n)` and
   `Nat.self_lt_two_pow_add : forall a b, Lt a (pow 2 (add a b))`
   (`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`, new file) --
   general, self-contained arithmetic (no dependency on `size`/`testBit`
   machinery). `self_lt_two_pow_add` is the key tool: it lets a proof bound
   TWO independent values (`n`, `m`) by ONE common power of two (apply it at
   `a := n` and `a := m` with the other value folded into `b`) without any
   general `Le`-based `pow` monotonicity lemma -- this prelude has only the
   STRICT, same-base `pow_lt_pow_of_lt`.
2. **`Nat.lt_of_testBit`** (piece 3 of 4): admitted, axiom-free, on the
   FIRST real kernel-check attempt (only Rust-level `E0499`
   nested-mutable-borrow errors needed fixing first). Registered as
   `F:nat-lt-of-testbit` -- see that fact and the module doc in
   `bit_order.rs` for the full route (`N := add n (add m (succ i))`, split
   via the pre-existing `Nat.sumRange_split`, tails identified via
   `sumRange_congr`).

## Codomain verdict for `F:ml430-nat-lt-of-testbit-72f64ab8`

Detail moved to [`../notes/265-nat-msb-order.md`](docs/plan/notes/265-nat-msb-order.md).

**Your lane's block (`OPEN`, nat-lor-assoc, 2026-08-29).** `Nat.land_assoc`
closed today after five lanes (`docs/plan/status/261-nat-land-assoc-finish.md`).
This lane's task was the `lor` counterpart, explicitly flagged as **not** a
transport — and it is not: the direct analogue of land's zero-propagation
lemma is FALSE for `lor`, confirmed by exhaustive Python simulation before
any Rust. What landed: the correct replacement invariant, kernel-verified
and tested, plus a complete, numerically-cross-checked derivation for
everything else `lor_assoc` needs. `F:ml430-nat-lor-assoc-82c4d0fd` remains
`open` — this lane did not close it, but leaves the hard mathematical
content (the invariant) done and the remaining assembly fully traced.

## What landed and is kernel-checked

**`Nat.lor_aux_ne_zero_of_right_ne_zero : ∀ fuel m n, Not (Eq n 0) →
Not (Eq (lorAux fuel m n) 0)`** (`rec_agreement.rs`), unconditional in
`fuel` — at `fuel = 0`, `lorAux 0 m n` is defeq `n` regardless of `m`
(the zero-fuel row ignores its first value argument entirely), so the
statement AT `fuel = 0` is literally the identity function on the
hypothesis. Built via `agree_by_fuel_induction`:

Detail moved to [`../notes/266-nat-lor-assoc.md`](docs/plan/notes/266-nat-lor-assoc.md).

**`F:ml430-nat-lor-assoc-82c4d0fd` is now `proved`.** This lane executed
`docs/plan/status/266-nat-lor-assoc.md`'s fully hand-traced,
Python-simulated derivation, verifying every step against the actual
`guarded`/`agree_by_fuel_induction`/`agree_by_double_fuel_induction`
signatures rather than trusting the prose. All four traced pieces held on
the first kernel-check attempt after one self-caught wiring bug (below);
`lor_aux_le_add` -- the ONE piece the tracing lane flagged as not
sub-step-verified in Python -- held exactly as specified, with no break.

## What was built (`rec_agreement.rs`)

Detail moved to [`../notes/267-nat-lor-assoc-exec.md`](docs/plan/notes/267-nat-lor-assoc-exec.md).

**Your lane's block (`DONE (Nat.xor_xor_cancel_left/_right landed, axiom-free; F:ml430-nat-lt-xor-cases-c43a1e85 stays open, 1 sub-target remains: Nat.xor_ne_zero_iff)`, nat-xor-cancel, 2026-08-29).**

## What landed

Both remaining sub-targets of piece 4 (`docs/plan/status/264-nat-xor-algebra.md`
diagnosed the route and left these two, plus the round-trip lemma, for this
lane):

```
Nat.xor_xor_cancel_left  : ∀ a b, Eq (xor a (xor a b)) b
Nat.xor_xor_cancel_right : ∀ a b, Eq (xor (xor a b) b) a
```

Both admitted axiom-free on the first successful attempt after one bisected
fix (see below), both with concrete-discriminating + symbolic evaluation
tests, both registered as new local facts (`F:nat-xor-xor-cancel-left`,
`F:nat-xor-xor-cancel-right`; neither has an `ml430` mirror — same reasoning
as `F:nat-xor-assoc`, recorded in full there).

All new code lives in `crates/axeyum-lean-kernel/src/nat_prelude/xor_algebra.rs`
(the file the brief assigned this lane), plus the minimal `nat_prelude.rs`
NameId registration and `nat_prelude_tests.rs` coverage-list/test additions
the brief said were expected.

## The `y <= 1` round-trip lemma — exact statement and route

`round_trip_le_one(d, p, y, h_le) : Eq (digitize (beq y 1)) y`, given
`h_le : Le y 1`, where `digitize(cond) := bool_select_nat cond 1 0`.

Detail moved to [`../notes/268-nat-xor-cancel.md`](docs/plan/notes/268-nat-xor-cancel.md).

**Your lane's block (`PARTIAL (cheap half landed as F:nat-testbit-eq-zero-of-lt; hard half NOT built, precise diagnosis below)`, nat-msb-exists, 2026-08-29).**

## What landed

**`Nat.testBit_eq_zero_of_lt : forall n j, Lt n (pow 2 j) -> Eq (testBit n
j) zero`** (`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`) --
admitted, axiom-free, on the FIRST real kernel-check attempt (only a
`clippy::doc_markdown` nested-backticks nit needed fixing afterward).
Registered as `F:nat-testbit-eq-zero-of-lt`. This is exactly the "cheap
half" `docs/plan/status/265-nat-msb-order.md` diagnosed but did not build:
above a value's own magnitude bound, every bit reads zero.

Route: `value_eq_sum_range` (already in `bit_order.rs`, private) at
`bound := j` gives `sumRange f_n j = n` directly from the hypothesis (via
`mod_eq_self_of_lt`); the same helper at `bound := succ j` needs
`n < pow 2 (succ j)`, obtained via `pow_j <= pow_j + pow_j = mul pow_j 2`
(`= pow 2 (succ j)` by `pow_succ`/`refl`), bridged with `le_add_right` +
`double_eq` (the exact same bridge `Nat.self_lt_two_pow_add`'s induction
step already uses) composed with `lt_of_lt_of_le`. `sum_range_succ` then
forces `n = add n (f_n j)` (substituting the first equation), so
`add_left_cancel` against `n = add n 0` collapses `f_n j` to `0`; since
`f_n j` is literally `mul (testBit n j) (pow 2 j)` up to beta,
`mul_eq_zero` splits into `testBit n j = 0` or `pow 2 j = 0`, and
`pow_pos` + `lt_irrefl` + `Or.resolve_right` rule out the second
disjunct. No new general arithmetic lemma was needed beyond what
`self_lt_two_pow_add`'s own proof already established the technique for.

## Codomain verdict for the Mathlib mirror

Detail moved to [`../notes/269-nat-msb-exists.md`](docs/plan/notes/269-nat-msb-exists.md).

**Your lane's block (`DONE (Nat.xor_ne_zero_iff landed, axiom-free; F:ml430-nat-lt-xor-cases-c43a1e85 stays open -- all four piece-4 sub-targets now landed, three larger pieces remain)`, nat-xor-ne-zero, 2026-08-29).**

## The exact statement

Read directly from the pinned Batteries checkout
(`/data0/axeyum/lean-import-toolchain/mathlib4/.lake/packages/batteries`,
commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`),
`Batteries/Data/Nat/Bitwise/Lemmas.lean:68`:

```lean
theorem xor_ne_zero_iff {x y : Nat} : x ^^^ y ≠ 0 ↔ x ≠ y := by simp
```

Confirms the "Lean core, not Mathlib-authored" reading `docs/plan/status/264-nat-xor-algebra.md`
and `docs/plan/status/268-nat-xor-cancel.md` already established for its three
siblings (`xor_assoc`, `xor_xor_cancel_left`, `xor_xor_cancel_right`, all also
in the same Batteries file, lines 51-60). No `ml430` fact exists to flip, so
this lands as a new local fact, `F:nat-xor-ne-zero-iff`.

## What landed

`Nat.xor_ne_zero_iff : ∀ a b, Iff (Not (Eq (xor a b) 0)) (Not (Eq a b))`,
admitted axiom-free on the first successful attempt (after fixing a compile
error, no `TypeMismatch` from the kernel at all — this route never poisoned
the shared prelude build), in `crates/axeyum-lean-kernel/src/nat_prelude/xor_algebra.rs`.

Detail moved to [`../notes/270-nat-xor-ne-zero.md`](docs/plan/notes/270-nat-xor-ne-zero.md).

**Your lane's block (`DONE (F:nat-exists-most-significant-bit landed, admitted axiom-free on the first attempt)`, nat-msb-hard, 2026-08-29).**

## What landed

**`Nat.msb_exists_of_le_fuel : ∀ fuel n, Le n fuel → Not (Eq n zero) →
∃ i, And (Eq (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j) zero)`**
(fuel-generalized) and **`Nat.exists_most_significant_bit`** (the `fuel :=
n` specialization via `le_refl`), both in
`crates/axeyum-lean-kernel/src/nat_prelude/bit_order.rs`. Both admitted,
axiom-free, on the FIRST real kernel-check attempt -- the entire
construction (~450 lines) compiled and kernel-checked without a single
`TypeMismatch` iteration. Registered as `F:nat-exists-most-significant-bit`.

This is the "hard half" both `docs/plan/status/265-nat-msb-order.md` and
`docs/plan/status/269-nat-msb-exists.md` diagnosed but did not build: the
highest bit really IS set, not just that no higher bit is needed.

## Does `Nat.size` shortcut this? No -- re-confirmed, not newly discovered

Re-read `binary.rs`'s `size` addendum before writing anything, per the
brief. `Nat.size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux
fuel n))` is proved by induction on `fuel` generalized over `n`, and it is
an UPPER bound only. It has no lemma relating `size n` to `size (n/2)` when
`n != 0` -- deliberately, since generalizing over ANY sufficient fuel is
exactly what let that proof avoid needing that relation. The route below
does not touch `size` at all; it is an independent fuel-recursion.

## Route taken: (b), an independent fuel-recursion -- NOT a `size`-recursion lemma

Detail moved to [`../notes/271-nat-msb-hard.md`](docs/plan/notes/271-nat-msb-hard.md).

**Your lane's block (`DONE (F:ml430-nat-lt-xor-cases-c43a1e85 CLOSED -- Nat.xor_trichotomy and Nat.lt_xor_cases both admitted axiom-free on the first real kernel-check attempt)`, nat-lt-xor-cases-final, 2026-08-29).**

## What landed

New file `crates/axeyum-lean-kernel/src/nat_prelude/xor_trichotomy.rs`:

```
Nat.xor_trichotomy : ∀ a b c, Not (Eq (xor (xor a b) c) 0) →
  Or (Lt (xor b c) a) (Or (Lt (xor c a) b) (Lt (xor a b) c))
Nat.lt_xor_cases : ∀ a b c, Lt a (xor b c) →
  Or (Lt (xor a c) b) (Lt (xor a b) c)
```

Both admitted, axiom-free, on the FIRST real kernel-check attempt — no
`TypeMismatch` from the kernel at any point (only one Rust-level `E0499`
nested-mutable-borrow error needed fixing before `cargo check` passed, and
two more before the evaluation test compiled). This closes
`F:ml430-nat-lt-xor-cases-c43a1e85`, the last row `docs/plan/status/
260-nat-lt-xor-cases.md` identified as reachable, now that all four
blocking pieces landed earlier the same day:

1. `Nat.testBit_xor` (`F:nat-testbit-xor`, `testbit_bitwise.rs`)
2. `Nat.exists_most_significant_bit` (`F:nat-exists-most-significant-bit`,
   `bit_order.rs`, via `Nat.msb_exists_of_le_fuel`)
3. `Nat.lt_of_testBit` (`F:nat-lt-of-testbit`, `bit_order.rs`)
4. `Nat.xor_assoc`/`Nat.xor_xor_cancel_left`/`_right`/`Nat.xor_ne_zero_iff`
   (`F:nat-xor-assoc`, `F:nat-xor-xor-cancel-left`/`_right`,
   `F:nat-xor-ne-zero-iff`, `xor_algebra.rs`)

## Codomain check: confirmed, an honest flip

Detail moved to [`../notes/272-nat-lt-xor-cases-final.md`](docs/plan/notes/272-nat-lt-xor-cases-final.md).

**Your lane's block (`WIP`, logic-excluded-middle, 2026-08-29).** Task was
`F:excluded-middle-not-intuitionistic` (one of five open facts outside the
Mathlib-mirror population). Step 0 (mandatory) was to determine what this
kernel already has toward a syntactic underivability result, before building
anything, and report honestly if the fact needs a substantial new
development.

**What exists in the kernel toward this, confirmed by reading source and
`kernel.environment()`, not by inventory tool:**

- No inductive type of syntactic formulas or derivations existed anywhere in
  the kernel before this lane (confirmed by
  `ipc_heyting::tests::no_prior_derivation_relation_exists_before_this_file`,
  which greps `kernel.environment()` for `Provable`/`Derivation`/`.Deriv`
  after building this lane's own prelude, paired with a positive control —
  `Formula`, this lane's own new declaration — so the negative cannot pass
  vacuously).
- The inductive-type list a prior lane enumerated
  (`True/False/And/Or/Iff/Eq/Exists/Acc/Bool/Nat/Decidable` + `Nat.le` +
  `Nat.Fin` + `Char` + `Nat.Pair`) is still current as far as this lane's
  grep of `add_inductive`/`add_datatype_family`/`add_recursive_datatype_family`
  call sites showed; nothing landed since adds a formula/derivation/proof-
  system type.
- The logic prelude (`prelude.rs`) already carries a substantial, genuinely
  useful family of Prop-generic results **around** excluded middle —
  `not_not_em : ¬¬(p ∨ ¬p)`, and the equivalences `dne_of_em`, `em_of_dne`,
  `peirce_of_em`, `em_of_peirce` — but every one is either a double-negation
  of `p ∨ ¬p` or a conditional equivalence taking EM/DNE/Peirce as a
  hypothesis. None is an instance of EM itself, and none is a derivation
  relation. This is the closest existing analogue and is NOT what the fact
  needs.
- **Generic infrastructure that DOES help**: `Kernel::add_recursive_datatype_family`
  (`prelude.rs`, already exercised in production by `string_prelude`'s `Str`
  and by the `IntList` example in `prelude/prelude_tests.rs`) builds exactly
  the AST shape a `Formula` type needs — mixed opaque-carrier / self-
  referential fields, non-parametric, non-indexed.

**Decomposition** (recorded in full, with rationale, in the module docs of
`crates/axeyum-lean-kernel/src/ipc_heyting.rs`):

Detail moved to [`../notes/273-logic-excluded-middle.md`](docs/plan/notes/273-logic-excluded-middle.md).

**Your lane's block (`DONE (3 new kernel-reconstructed sibling facts landed;
verified the 28-fact cas-internal backlog is unchanged and re-confirmed its
cluster breakdown; two clusters identified as genuinely needing new kernel
machinery, not cheaply reachable)`, cas-row-three, 2026-08-29).**

## Starting measurement (verified myself, step 0)

`python3 scripts/validate-facts.py` at the start of this lane:

    cas-certificate: 32 total -- kernel-reconstructed 4, cas-internal 28

Matches `docs/research/11-design-review/2026-08-28-ivt-evt-pareto-position-measured.md`'s
"Row 3, followed up" section exactly.

## Cluster breakdown of the 28 cas-internal facts — re-verified, unchanged

Wrote a small script classifying every `cas-certificate` fact via
`scripts/validate-facts.py`'s own `classify_cas_certificate_fact`, then
grouped the 28 cas-internal ones by name prefix:

Detail moved to [`../notes/274-cas-row-three.md`](docs/plan/notes/274-cas-row-three.md).

**Your lane's block (`DONE (the empty-queue gate and the divergence screen landed; refill and drift are written proposals)`, autogenesis-refill, 2026-08-29).**

Status: **(1) and (2) landed; (3) and (4) are written proposals, deliberately
not executed — see "What this lane did NOT do".**

Everything below was re-measured in this worktree after `git merge main`, not
read from the design-review note. Where the note and the measurement differ, the
measurement is stated and the difference is named.

---

## Step 0 — re-measurement (2026-08-29)

The numbers in
[`docs/research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md`](docs/research/11-design-review/2026-08-29-the-mirror-population-is-consumed.md)
reproduce exactly.

| | measured |
| --- | --- |
| facts total | 1,949 |
| `ml430` population | 214 |
| `ml430` proved | 155 (72.4%) |
| `ml430` open | 59 |
| open, all facts | 64 — so the **non-mirror open set is 5** |
| nursery entries | 216 (train 78 / development 99 / held-out 37 / longitudinal 2) |

Two things the note does not say, both of which sharpen it.

**The dispatchable set is 1, not ~12.** The note's "~12 dispatchable, of which
11 are structurally blocked" is right, and the residue is a single row:
`F:ml430-nat-lt-xor-cases-c43a1e85`, which is in flight. Eleven blocked rows,
four constructions:

```
Nat.testBit      codomain             5 rows
Nat.multichoose  definitional         3 rows
Nat.minFac       algorithmic          1 row
Nat.fastFib      recursion-principle  1 row  (+ Nat.testBit accounts for
                                              testbit_eq_inth, the 11th)
```

**The 37 open held-out rows are exactly two families.** Not spread across the
population — `natural-logarithm` (21) and `natural-square-root` (16). Every
other held-out family is fully closed. Confirmed against
`mathlib-nursery-split-policy-v1.json`, whose `family_partitions` assigns
exactly those two to `held-out` out of twelve families. So the blind evaluation
population is not merely off-limits; **what remains of it tests exactly two
capabilities**, and a refill that does not add held-out breadth leaves the
evaluation narrow even if it never spends a row.

---

## (1) The selection mechanism — what would have reported an empty queue

Answer: **nothing would have, and one thing that comes close has been red on
`main` with nobody running it.**

### `scripts/fact-frontier.py` — prints the bands, cannot report emptiness

It is the tool that turns the ledger into a queue, and it is better than the
note implies: it already annotates every held-out row with a ⛔ marker naming
ADR-0542's cost, marks every mutation control, and prints

Detail moved to [`../notes/275-autogenesis-refill.md`](docs/plan/notes/275-autogenesis-refill.md).

**`just check`'s stack-envelope step was RED on `main` for `integer`, `cpoint`
and `complex`. All three re-derived to a clean passing power of two —
resource growth, not a proof bug** (`DONE`, stack-envelope-remeasure,
2026-08-29).

## What was measured

`scripts/check-kernel-stack-envelope.sh --measure --profile release --prelude
<p>` for each of the three failing preludes, each bisecting cleanly to a
passing power of two (confirmed independently for `cpoint` and `complex` with
direct probes at the bisected value and at half of it):

| prelude | old release pin | new release pin | ratio |
|---|---:|---:|---:|
| `integer` | 65,536 | 131,072 | 2× |
| `cpoint` | 1,048,576 | 8,388,608 | 8× |
| `complex` | 262,144 | 8,388,608 | 32× |

Debug rows were re-checked too, since the pin file carries debug columns for
all three:

| prelude | old debug pin | new debug pin | moved? |
|---|---:|---:|---|
| `integer` | 262,144 | 262,144 | no (confirmed by `--measure`) |
| `cpoint` | 33,554,432 | 33,554,432 | no (confirmed by direct probe: passes at 33,554,432, fails at 16,777,216 — same bisection as before) |
| `complex` | 4,194,304 | 16,777,216 | yes, 4× — the OLD debug pin now fails |

## The hypothesis was tested and refuted

I was briefed to test whether `nat`'s same-day growth (`Nat.Pair`,
`Nat.binaryRec`, the `land`/`lor`/`ldiff`/`xor` bitwise family with its
comm/assoc/`*_bit` lemmas) drove all three failures uniformly as downstream
consumers. It does not:

Detail moved to [`../notes/276-stack-envelope-remeasure.md`](docs/plan/notes/276-stack-envelope-remeasure.md).

**Your lane's block (`DONE (multivariate bridge landed with one reconstructed
fact; kernel-reconstructed 7 → 8; the arity survey refutes the fixed-arity
alternative for geometry and CONFIRMS it for WZ, so the two clusters do NOT
share one dependency)`, cas-multivariate, 2026-08-29).**

## Step 0: the sizing in `docs/plan/status/274-cas-row-three.md` re-verified

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 35 total -- kernel-reconstructed 7, cas-internal 28

Unchanged, and the cluster breakdown (NRA geometry 10, WZ 9, gf2 4,
real-algebraic 4, partial fractions 1) matches.

## The arity survey — measured from the certificates, not from the fact statements

### Geometry (10): arities 6–19. **The fixed-arity alternative is REFUTED.**

`artifacts/geometry-certificates/*.json` carry the actual `MvPoly` data:

| certificate | coords | sat vars | generators | conclusions | total vars | max total degree | max terms in one poly | total terms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| thales-right-angle-in-semicircle | 6 | 0 | 1 | 1 | 6 | 2 | 8 | 17 |
| medians-concurrent | 8 | 0 | 2 | 1 | 8 | 2 | 10 | 32 |
| orthocentre-altitudes-concurrent | 8 | 0 | 2 | 1 | 8 | 2 | 8 | 26 |
| parallelogram-diagonals-bisect | 8 | 1 | 3 | 2 | 9 | 3 | 8 | 47 |
| centroid-divides-medians | 8 | 1 | 3 | 2 | 9 | 3 | 10 | 55 |
| rhombus-diagonals-perpendicular | 8 | 1 | 4 | 1 | 9 | 3 | 12 | 73 |
| pappus-hexagon | 18 | 1 | 9 | 1 | 19 | 3 | 10 | 137 |
| euler-line | 10 | 1 | 5 | 1 | 11 | 6 | 74 | 331 |
| simson-line | 14 | 3 | 10 | 1 | 17 | 9 | 324 | 1992 |
| varignon-midpoint-parallelogram | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0 |

No small fixed arity covers even two of the ten. A bivariate/trivariate bridge
buys nothing here.

Detail moved to [`../notes/277-cas-multivariate.md`](docs/plan/notes/277-cas-multivariate.md).

**Your lane's block (`DONE (the statable-here screen landed; 80 rows
preregistered; the empty-queue gate is green at 50 dispatchable)`,
nursery-refill-exec, 2026-08-29).**

---

## Step 0 -- re-measurement

`scripts/check-dispatchable-frontier.py` was **red on `main`**, as briefed, and
the number is one lower than the previous lane recorded (a mirror closed in
between):

```
FAIL: G4 empty-dispatchable-set
open ml430 mirrors: 58
  held-out (blind evaluation, do not dispatch): 35
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 0
```

### One correction to the previous lane's record

[`275-autogenesis-refill.md`](docs/plan/status/275-autogenesis-refill.md) names the pinned
statement source as `mathlib-v4.30.0-nat-int-statement-inventory-v1.ndjson`.
**The pinned artifact is `-v2`**, and the two are different files:

| file | sha256 | pinned by |
| --- | --- | --- |
| `…-inventory-v1.ndjson` | `b3569d54…` | nothing in the tree |
| `…-inventory-v2.ndjson` | `4285e551…` | ADR-0479, `mathlib-statement-source-v1.json`, and 15 scripts |

Both carry 9,729 records, which is why the substitution is invisible from a
record count. This lane reads **v2** and pins its sha256 in the generator.

---

## (1) The positive "statable here" screen

### The idea

The divergence registry is a **negative** screen: it names constructions whose
axeyum counterpart diverges. It says nothing about whether a proposition can be
*expressed* here at all, which is why hundreds of `Std.PRange`, `Finset` and
`LinearOrder` rows pass it.

The positive screen answers the complementary question **from
`kernel.environment()`**, never from a theorem inventory (which lists no
`Definition`s -- `Nat.add` returns zero rows from `prelude_theorem_inventory`
and certainly exists).

A pinned statement's `type_repr` is a structural `Lean.Expr` dump, so its Lean
constants are extractable mechanically (`Lean.Expr.const `Nat.fib []` ->
`Nat.fib`). A candidate is **statable here** iff every constant is admissible:

```
  env      2,207 declaration names read from kernel.environment()
           (examples/shape_search --include-constructed, all six populated
           kinds; snapshot in artifacts/autogenesis/kernel-environment-snapshot-v1.json)
+ bridge      70 Lean surface constants NOT in the environment but appearing in
           the pinned statement of a mirror we have ALREADY CLOSED
```

Detail moved to [`../notes/278-nursery-refill-exec.md`](docs/plan/notes/278-nursery-refill-exec.md).

**Your lane's block (`DONE (all three gates fixed; the third was not what it
looked like)`, gate-rot-triage, 2026-08-29).**

Verdicts, one line each: **1) STALE** (`check-fact-depends-derived.py`) —
the ledger, not the checker, was behind. **2) STALE FIXTURE, GUARD SOUND**
(`test_check_autogenesis_nat_fib_gcd_premise_selection_policy.py`) — real
proof work advanced the chain the fixture assumed was frozen. **3) BROKEN
SCANNER, DISGUISED AS A STALE BASELINE** — this is the one worth reading
carefully, because the naive fix (lower the number to match a fresh count)
would have been actively wrong.

## 1. `check-fact-depends-derived.py` — STALE, and by a lot

Reproduced before touching anything: `missing_edges=1054` across 306 facts
(kernel_facts=1808, graph=1770), not the small drift a "~30 facts landed
today" framing suggested. 182 commits touched `artifacts/facts/` since this
gate was last green (`233331935`, 2026-08-25). This checker needs a
`--release` build of `theorem_dependency_inventory`, which is the expensive
step every lane has been skipping while re-verifying narrowly — exactly the
mechanism CLAUDE.md's flywheel section warns about.

Spot-checked one failure before trusting the bulk fix:
`F:cassini-identity-over-constructed-integers` already `depends_on`
`F:ml430-nat-fib-add-two-b86e0c82` (an ADR-0603 mirror fact) for the same
underlying theorem `Nat.fib_add_two`, but not `F:nat-fib-add-two` — the
native fact whose evidence actually names that kernel theorem via
`theorem_dependency_inventory`, which is the one this checker's
theorem-to-fact map resolves to. Real gap, not a checker artifact.

Detail moved to [`../notes/279-gate-rot-triage.md`](docs/plan/notes/279-gate-rot-triage.md).

**Fixed and committed** (`WIP`, solver-cycle-regression, 2026-08-29).

## What the gate actually said (correcting the task text)

The exact FAIL text this task was handed — `NEW CYCLE MEMBERS: grp, x`,
`LARGEST CYCLE GREW: 0 -> 3 lines (from nothing)`, `LARGEST CYCLE GREW:
2 -> 802 lines (401.00x)` — is **not from `scripts/analyze_solver_module_graph.py
--check`**, the gate `check.sh` actually runs (`scripts/check.sh:711`). It is
stdout from `scripts/tests/test_analyze_solver_group_collapse.py`'s own
mutation-control fixtures: `grp`/`x` are literal synthetic module names that
test file constructs on purpose to prove the guard fires on a deliberately-bad
grouping. Confirmed by running that suite directly: **14/14 tests pass**, and
the "401x" figure is also independently a *documented historical example* in
`analyze_solver_module_graph.py`'s own source comments (a 2026-08-17 measurement
on a proposed `arith/` directory, never landed). Neither is a live regression.

The real gate, run directly (`python3 scripts/analyze_solver_module_graph.py
--check`), reported different names and different numbers throughout this
investigation — see below.

## When and why (the real regression)

`docs/refactor-2026-08/solver-module-graph-baseline.json` was last written by
commit `90ef09a80` on **2026-08-17 09:32:14 -0400**. The gate has been red
since **~11:27 that same day** — 12 days as of this writing, unrelated to any
lean-kernel work from today. Two commits landed in the intervening two hours,
each independently closing a previously-acyclic module into the 26-module
theory-core cycle:

Detail moved to [`../notes/280-solver-cycle-regression.md`](docs/plan/notes/280-solver-cycle-regression.md).

**Closed all ten dispatched facts** (`DONE`, int-order-add, 2026-08-29).

## Step 0 finding: one of ten already existed

`Int.add_le_add` (`F:ml430-int-add-le-add-a76ad5ce`) was already declared in
`int_prelude/order.rs::declare_additive_order`, built from the `sub_nat_nat`
difference-witness technique (destructure each `le` hypothesis into an
explicit non-negative gap, re-associate, read the conclusion off the trivial
direction — no `Int.rec` case split). This fact closed as a pure status flip
plus evidence attachment: no new proof was written for it. Confirmed absent
under any other name first via `prelude_theorem_inventory --release
--include-constructed` before concluding the other nine were genuinely new.

## The other nine: `crates/axeyum-lean-kernel/src/int_prelude/order_add.rs`

All nine build as pure algebra on top of three already-derived facts —
`Int.add_le_add`, `Int.add_neg_cancel_right` (`algebra.rs`), and `modeq.rs`'s
private `cancel_neg_add`/`cancel_neg_add_left` (the latter widened from
`fn` to `pub(super)`, the only change outside the new file and
`int_prelude.rs`'s field/dispatch wiring). **No `Int.rec` case split anywhere
in the new file** — this is exactly why the task's "should be cheap"
framing held:

- `Int.add_le_add_left` / `Int.add_le_add_right` — `add_le_add` with a
  `le_refl` on the fixed side.
- `Int.add_le_add_iff_left` / `Int.add_le_add_iff_right` — `mpr` is the
  left/right corollary above; `mp` shifts the hypothesis by the common
  term's negation and collapses with `cancel_neg_add_left` /
  `add_neg_cancel_right`.
- `Int.add_le_add_three` — two applications of `add_le_add`.
- `Int.add_le_iff_le_sub` — `mp`/`mpr` shift by `-b` and collapse with
  `add_neg_cancel_right` / `cancel_neg_add`.
- `Int.add_le_of_le_neg_add`, `Int.add_le_of_le_sub_left`,
  `Int.add_le_of_le_sub_right` — each shifts the hypothesis by `a` (or `b`)
  itself via `add_le_add` and collapses with a small `a + (-a + x) = x`
  identity (`add_cancel_neg_left`, new, the mirror image of
  `cancel_neg_add_left` with `a` and `-a` swapped) or `cancel_neg_add`.

`Int.sub a b := add a (neg b)` is `ReducibilityHint::Regular`
(`sub.rs`), so every statement using `c - b` is stated **folded** (matching
the Mathlib form being mirrored) and proved against the **unfolded**
`add c (neg b)` throughout — `add_declaration`'s own defeq check bridges the
two, per that module's documented convention. No explicit fold/unfold calls
were needed anywhere.

## Mirror-flip check

Detail moved to [`../notes/281-int-order-add.md`](docs/plan/notes/281-int-order-add.md).

**Your lane's block (DONE, int-parity-two, 2026-08-29).** Ten freshly-dispatched
`ml430` mirrors; **7 closed, 3 left open**. None of the ten already existed
under a different name (checked `int_prelude/parity.rs`, the only prior
`Int.Even`/`Int.Odd` content, before starting — it had only the two
definitions and the two `natAbs` bridge theorems from the `int-parity` lane).
The `Nat` parity bridge (`Nat.even_iff_mod_two_eq_zero`,
`Nat.odd_iff_mod_two_eq_one`, `Nat.mod_two_eq_zero_or_one`) did transport, but
not by direct reuse of a `Nat`-side theorem name — each Int fact needed its
own `Int.rec` case split with the `Nat` lemma applied to the bound `Nat` field
of whichever branch, because `Int.Even`/`Int.Odd` are defined via `natAbs`,
not via a fresh `Int`-level existential (the `int-parity` lane's design
choice, module doc in `parity.rs`).

**Closed (all axiom-free, `derived_laws` 160 -> 168):**

Detail moved to [`../notes/282-int-parity-two.md`](docs/plan/notes/282-int-parity-two.md).

**Lane block (`DONE for this dispatch`, nat-div-mod-family, 2026-08-29).**

**The task.** Nine freshly-preregistered `ml430` `Nat` division/modulo
mirrors were dispatchable (`python3 scripts/check-dispatchable-frontier.py`
confirmed these are exactly the `nat-`-family entries in the 50-item
dispatchable set, no others among the "div"/"mod" hits — the rest of that
grep is `nat-lcm-div`, which is a different family, and the `int-` ediv/emod
entries, out of scope for this lane):

```
F:ml430-nat-add-div-left-1b15b2b2          F:ml430-nat-add-div-right-4b60b393
F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0
F:ml430-nat-add-mod-left-6b337077          F:ml430-nat-add-mod-right-c047c67a
F:ml430-nat-add-mul-div-left-e20827dd      F:ml430-nat-add-mul-div-right-44a689e4
F:ml430-nat-add-mul-mod-self-left-108b5fe0 F:ml430-nat-add-mul-mod-self-right-ac5b3624
```

**Closed, 8 of 9.** All landed as fresh local constructions (Step 0's
absence check confirmed none of these were already proved under a different
name — no existing declaration matched any of the eight shapes) —

- `Nat.add_mul_div_left`, `Nat.add_mul_div_right`
- `Nat.add_mul_mod_self_left`, `Nat.add_mul_mod_self_right`
- `Nat.add_mod_left`, `Nat.add_mod_right`
- `Nat.add_div_left`, `Nat.add_div_right`

New file `crates/axeyum-lean-kernel/src/nat_prelude/div_mod_lemmas.rs`. All
eight reduce to one reusable fact, `div_mod_shift(d, p, dd, pos_dd, n, k)`:
for a positive divisor `dd` and any `n, k`, `(n+dd*k)/dd = n/dd+k` and
`(n+dd*k)%dd = n%dd`. That is built from `division.rs`'s
`div_mod_exec`/`div_mod_unique`/`div_mod_add_multiple` via a local
`div_mod_reconstructed` (a copy of `group.rs`'s private helper of the same
shape — established per-file pattern in this prelude, not a new one). The
four with no positivity hypothesis in the Mathlib statement
(`add_mod_left`/`_right`, `add_mul_mod_self_left`/`_right`) case-split their
divisor via `cases_zero_succ`; the zero branch collapses via
`zero_mul`/`mul_zero` plus `add_zero`, never touching division. `add_div_left`/
`add_div_right` are the `k := 1` instance of the `add_mul_div_*` shape after
an `add_comm`/`mul_one` bridge.

**Two real bugs found and fixed while landing this** (both in the commit
history, not left for the next lane):

Detail moved to [`../notes/283-nat-div-mod-family.md`](docs/plan/notes/283-nat-div-mod-family.md).

**Your lane's block (`DONE (4/6 fixed, 2 precisely diagnosed and left open — see
below for why)`, autogenesis-gate-rot, 2026-08-29).**

Assigned six gates from a stale (pre-merge) `scripts/check.sh` run. Reproduced
every one directly before touching anything. Verdicts:

1. **`autogenesis-mathlib-facts` — BROKEN by design, fixed.** `verify_outputs`
   compared every catalog fact byte-for-byte against a freshly regenerated
   `epistemic_status: open, evidence: []` stub. That invariant broke the moment
   ANY of 214 catalogued facts left `open` — which happened the same day the
   gate was added (`b9daf91a5`, 2026-08-18) — so it has been red for anyone who
   ran `--check` for 11 days; nobody had. Measured the diff set across all 156
   now-proved facts: only `provenance`, `notes`, `epistemic_status`,
   `proof_route`, `axiom_footprint`, `evidence`, `depends_on`, `concept_refs`,
   and `formal` (replaced wholesale on proof, per ADR-0601) ever diverge;
   `id`/`title`/`statement`/`external_status`/`schema_version` never do across
   all 156. Fixed `verify_outputs` to require byte-exact equality only while a
   fact is still `open`; for a settled fact, only those five invariant fields.
   Added 3 tests (settled-diverges-ok, settled-identity-corruption-still-fails,
   open-mutation-still-fails). Commit `64ae9166e`.

Detail moved to [`../notes/284-autogenesis-gate-rot.md`](docs/plan/notes/284-autogenesis-gate-rot.md).

**Your lane's block (`DONE (3 of 4 fixed; the 4th is a real crates/ defect, precisely diagnosed and reported, not touched)`, inventory-gate-rot, 2026-08-29).**

Assigned four gates that were RED on `main`: `example-inventory-count`,
`example-inventory-controls`, `lane-turn-controls`, `lra-hypothesis-binding`.
Reproduced each directly (never trusted the coordinator's older aggregate-gate
log). Verdicts:

1. **`example-inventory-count` — STALE.** `python3
   scripts/gen-example-inventory.py --check` reported both markers
   (`docs/documentation-plan.md`, `docs/plan/global/30-workstream-state.md`)
   still saying 193 while `git ls-files 'crates/*/examples/*.rs'` counts 202 —
   the ~15 new kernel example binaries that landed since the last
   regeneration. Regenerated; `--check` now passes (`stale=0`). This also
   staled `PLAN.md` (it quotes the same count via
   `docs/plan/global/30-workstream-state.md`), so `python3 scripts/gen-plan.py
   --check` had to be regenerated too.

2. **`example-inventory-controls` — STALE (downstream of #1), guard sound.**
   `scripts/tests/test-gen-example-inventory.sh`'s own first case ("a clean
   tree passes `--check`") was failing purely because the tree was NOT clean
   (see #1). Not a vacuous or broken control — once #1 was regenerated, all 6
   cases pass (`GEN_EXAMPLE_INVENTORY_CONTROLS|cases=6|failures=0`).

Detail moved to [`../notes/285-inventory-gate-rot.md`](docs/plan/notes/285-inventory-gate-rot.md).

**Lane block (`DONE for this dispatch`, nat-lcm-gcd, 2026-08-29).**

**The task.** Ten dispatchable `ml430` mirrors:

```
F:ml430-nat-lcm-comm-d5f8aae0        F:ml430-nat-lcm-assoc-cb00bb43
F:ml430-nat-lcm-div-eb5d8892         F:ml430-nat-lcm-dvd-07899eea
F:ml430-nat-dvd-lcm-left-c83bcebc    F:ml430-nat-dvd-lcm-right-18ab8e2f
F:ml430-nat-eq-zero-of-lcm-eq-zero-d09b7af7
F:ml430-nat-gcd-dvd-mul-81cb13df     F:ml430-nat-gcd-le-mul-7e3800f7
F:ml430-nat-gcd-mul-lcm-b7217ace
```

**Closed, 10 of 10.**

**Step 0 found five already proved under the identical statement**, before
any new proof work: `nat_prelude/lcm.rs` already declared `Nat.lcm_comm`,
`Nat.lcm_dvd`, `Nat.dvd_lcm_left`, `Nat.dvd_lcm_right`, and
`Nat.gcd_mul_lcm`, each matching its fact's `formal.statement` verbatim
(confirmed via `nat_theorem_inventory`'s rendered type, not by reading the
Rust source). Pure status flip plus evidence for these five, no proof work.

**Five new theorems**, all in a new file
`crates/axeyum-lean-kernel/src/nat_prelude/lcm_gcd_lemmas.rs`:

Detail moved to [`../notes/286-nat-lcm-gcd.md`](docs/plan/notes/286-nat-lcm-gcd.md).

**Lane block (`DONE for this dispatch`, nat-totient, 2026-08-29).**

**The task.** Nine freshly-preregistered `ml430` `Nat.totient` mirrors were
dispatchable:

```
F:ml430-nat-totient-eq-zero-3be161d6            F:ml430-nat-totient-eq-one-iff-68d883a0
F:ml430-nat-totient-even-28e0415f               F:ml430-nat-totient-dvd-of-dvd-9622e44a
F:ml430-nat-odd-totient-iff-b6a6596f            F:ml430-nat-odd-totient-iff-eq-one-d0491d84
F:ml430-nat-totient-coprime-totient-iff-3932cf83
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
F:ml430-nat-dvd-two-of-totient-le-one-3642bf31
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
```

**Step 0.** `Nat.totient` is a `Definition` (`nat_prelude/totient.rs`,
already there before this lane, along with `Nat.countRange` and one prior
theorem `Nat.totient_prime`). A theorem inventory returns zero rows for it
by construction — confirmed the trap doesn't apply here since the family's
own file already reads it from the environment/source, not from an
inventory. Checked which of the nine already existed under a different
name: **none did** — `theorem_dependency_inventory`/`prelude_theorem_inventory
--include-constructed --release` had no match for any of `totient_eq_zero`,
`totient_eq_one_iff`, `totient_even`, `totient_dvd_of_dvd`,
`odd_totient_iff{,_eq_one}`, `totient_coprime_totient_iff`,
`eq_or_eq_of_totient_eq_totient`, `dvd_two_of_totient_le_one`,
`totient_gcd_mul_totient_mul` before this lane, and `coprime_succ_self`
(the one new supporting lemma this lane needed) was also absent (`gcd_comm`,
`gcd_succ_self` too — the only prior `gcd_comm`-shaped fact in the tree is
`int_prelude`'s, over `Int` arguments).

Detail moved to [`../notes/287-nat-totient.md`](docs/plan/notes/287-nat-totient.md).

**Lane block (DONE, int-emod-additive, 2026-08-29).** The `int-parity-two`
lane closed 7 of 10 `ml430-int-*` division-by-two mirrors and left exactly
three open, all needing "an additive compatibility law for `emod` under
`Int.add`'s branch table" that it sized as a separate, comparably-large task.
This lane built that law and closed all three.

```
F:ml430-int-even-add-3c4536e3       F:ml430-int-even-add-bc8e1394
F:ml430-int-even-add-one-af33da18
```

**The law did NOT need a fresh `Int.rec` case split on `Int.add`'s branch
table**, contrary to the sizing in `docs/plan/status/282-int-parity-two.md`.
`Int.ModEq` (`modeq.rs`) already carries general additive congruences —
`mod_eq_add_right : ModEq n a b → ModEq n (a+c) (b+c)` and
`mod_eq_add_left : ModEq n a b → ModEq n (c+a) (c+b)` — and composing them
via `mod_eq_trans` gives the additive law directly:
`ModEq n a b → ModEq n c d → ModEq n (a+c) (b+d)` (`modeq_add`,
`parity.rs`). One composition, no new case analysis. This is the answer to
the brief's "check whether the `Nat` `div_mod_shift` shape transports"
question: **it did not need to** — `div_mod_shift`'s shape (shift a
dividend by an exact multiple of the divisor, via `div_mod_unique`) solves a
different problem than "what is `(m+n) % 2` given `m % 2`/`n % 2`", and the
`ModEq` route already in this prelude was the closer fit.

**The route, in full:**

Detail moved to [`../notes/288-int-emod-additive.md`](docs/plan/notes/288-int-emod-additive.md).

Lane: `diophantine-blowup`.

**Status: fixed, with a measured residual.** The immediate defect is a one-word
call-site bug and is landed. The Diophantine route's module size is still
superlinear in the coefficients, which is a separate, bounded piece of work
written up below rather than papered over.

---

## Step 0 — reproduced standalone, before reading any code

    target/release/examples/lean_hypothesis_binding_dump \
      artifacts/examples/math/number-theory-v0/smt2/diophantine-gcd-obstruction-conflict.smt2

    2.24 s wall, stdout = 96,297,506 bytes (91.8 MiB)
    stderr: BINDING_DUMP|...|fragment=Diophantine|assertions=1|indices=0

Independently confirms the finding lane's number.

## Where the size came from — measured, not suspected

The module is 234 lines. **One of them is 96,155,365 bytes — 99.85 % of the
file**: line 232, the body of `theorem axeyum_refutation : False :=`. The
next-largest line is 14,183 bytes. Not a diffuse blowup; a single proof term.

Hash-consing that one line back into a DAG (`scratchpad/dio-profile.py`, an
explicit-stack tokeniser over the 10.9 M-token line) gives the answer:

| | |
| --- | --- |
| distinct nodes in the term | **18,018** — 46 leaf, 17,972 application |
| printed as a tree | **96,155,363 bytes** |
| printed with full sharing (computed from the DAG) | **~967,245 bytes**, 99× smaller |
| most-repeated single distinct subterm | **169,184** occurrences |
| distinct app nodes occurring >10³ times | 291 |

Printed-byte attribution over that line, by occurrence count × own length:

    43,480,584  leaf `axeyum.reconstruct.dio.x._1`
    20,578,860  leaf `axeyum.reconstruct.dio.x._0`
    17,093,174  leaf `Int.add`
     9,767,528  `Int.add` application syntax
     1,705,104  leaf `Int.zero`

So **the dominant term is not any part of the argument — it is the tree
expansion of a small DAG.** The proof is a chain of `Eq.rec` rewrites
(30,527 occurrences, over `Int.add_assoc`/`add_comm`/`add_zero`), and a Lean
`Eq.rec` reprints its subject term about four times per step (the type index,
the motive body, the two endpoints). Nest hundreds of those and you get 4^depth
without a single large number anywhere.

### Root cause: the renderer was called at the wrong entry point

`crates/axeyum-lean-kernel/src/lean_pp.rs:885` builds a share plan **only under
`compact`**:

    let shares = if compact {
        self.compact_share_plan(&[goal, proof], theorem_name, &at_consts)
    } else {
        LeanSharePlan::default()
    };

and `reconstruct_diophantine_to_lean_module` called `render_lean_module` — the
non-compact one. So no sharing was attempted at all.

Detail moved to [`../notes/289-diophantine-blowup.md`](docs/plan/notes/289-diophantine-blowup.md).

**DONE (`depends-producer`, 2026-08-29).**

## What `--fix` does

`scripts/check-fact-depends-derived.py --fix` computes exactly the same
missing-edge set `evaluate()` would otherwise report as a failure (both now
share `_kernel_index`, and a new `missing_edges_by_fact()` collapses the
per-message traversal into a per-fact set), then patches each affected fact
file's `depends_on` array with a **surgical text substitution** — never a
JSON re-dump. `_patch_depends_on()` finds the file's own `"depends_on": [...]`
span via a non-nesting regex (`[^\[\]]*`, safe because no `depends_on` entry
in the whole ledger contains `[` or `]`), parses just that array, appends the
missing ids (sorted, deduped against what's already there), and re-emits it
in the array's OWN style: single-line stays single-line, multi-line keeps its
own entry indent and closing-bracket indent (read from the array itself, not
assumed — the committed ledger has dozens of distinct indent widths). If
nothing is missing, the function returns the input unchanged, byte for byte —
this is deliberately its own guard (see mutation results below), not an
accident of dict equality.

After writing, `fix()` **reloads every file from disk** (not from the
in-memory patch) and re-runs `evaluate()` as a self-check; if any edge is
still missing it reports the same `DEPENDS_DERIVED_ERROR|` lines and returns
1. This exists so a broken substitution is caught here, not by the next
process that reads these files.

Verified against the real ledger in a scratch copy (never the tracked
files): regressing `F-ml430-int-add-le-add-a76ad5ce.json`'s `depends_on` (both
a single-line and a hand-restored multi-line variant) and running the patch
restores exactly the missing edge, and a mask-diff (`depends_on` span blanked
out in both texts) is byte-identical outside that one field.

## Where the enforcement is wired, and why there

Enforcement lives in **`scripts/validate-facts.py`** (`run_depends_derived_gate`,
called from `main()` right after the structural-error check). Reasons, in
order:

Detail moved to [`../notes/290-depends-producer.md`](docs/plan/notes/290-depends-producer.md).

**DONE for this dispatch (`totient-counting`, 2026-08-29).**

**The task.** The nat-totient lane (`287-nat-totient.md`) closed 1 of 9
dispatched `ml430` `Nat.totient` mirrors and triaged the other 8 as
bottlenecking on three pieces: (1) a general "two distinct witnesses ⇒
count ≥ 2" lemma, (2) the fixed-point-free-involution pairing argument for
`totient_even`, (3) the multiplicative formula
`totient(mn) = totient(m)·totient(n)`. This lane was pointed at a candidate
shortcut for piece 2 (`Int.prod_range_pairing_collapse`,
`int_prelude/wilson.rs`) and asked to check it before building anything,
then pick one piece and land it.

**Checked the pointer first.** `Int.prod_range_pairing_collapse` is a real,
general fixed-point-free-involution/pairing lemma — but it collapses an
`Int.prodRange` to `1` under `ModEq`, over a Wilson-specific concrete
`sigma := Nat.inverseIndex`. It does **not** transport to "a
`Bool`-predicate-defined `Nat.countRange` subset has even cardinality"
without re-deriving the whole two-step structural induction against a
`Nat`-valued (not `Int.ModEq`-valued) conclusion, over a `Nat.countRange`
domain rather than `Int.prodRange`. That is genuinely separate work, not a
corollary — recorded in `totient_lemmas.rs`'s module doc so the next lane
on `totient_even` does not re-check this.

**Chose piece 1** (the general witness-counting lemma) instead, because
unlike pieces 2/3 it needed **no new induction principle** — only
composition of `Nat.countRange`'s existing defining equation
(`countRange_succ`, itself proved by `Eq.refl`) with `le_dest`/`exists_rec`
(already in `order.rs`, the same shape `le_of_add_le_add_left` uses).

**Landed, axiom-free, in `nat_prelude/totient_lemmas.rs`:**

Detail moved to [`../notes/291-totient-counting.md`](docs/plan/notes/291-totient-counting.md).

**Lane block (`DONE -- well-founded refusal, plus a reusable already-proved screen`, nursery-refill-two, 2026-08-29).**

## Step 0 -- re-measurement (main merged, everything re-run)

```
python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 99
  held-out (blind evaluation, do not dispatch): 65
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 11
      F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0
      F:ml430-nat-base-induction-83561d4c
      F:ml430-nat-dvd-two-of-totient-le-one-3642bf31
      F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      F:ml430-nat-odd-totient-iff-b6a6596f
      F:ml430-nat-odd-totient-iff-eq-one-d0491d84
      F:ml430-nat-totient-coprime-totient-iff-3932cf83
      F:ml430-nat-totient-dvd-of-dvd-9622e44a
      F:ml430-nat-totient-eq-one-iff-68d883a0
      F:ml430-nat-totient-even-28e0415f
      F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
exit 0
```

9 of the 11 are `natural-totient`, matching the brief's "a lane is actively
working" note.

```
python3 scripts/check-autogenesis-holdout-isolation.py
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Matches the brief's quoted baseline exactly.

## The ceiling is the binding constraint -- worked out from the generator's own rules

```
artifacts/autogenesis/nursery-v1.json entries:            216  (214 evaluation + 2 amendments)
artifacts/autogenesis/nursery-v2-extension.json entries:   80
V1_EVALUATION_ENTRIES (frozen constant in the generator):  214
EVALUATION_CEILING:                                        300
current total (R3's own formula, 214 + 80):                294
headroom:                                                    6
```

`gen-autogenesis-nursery-refill.py` regenerates the WHOLE `nursery-v2-extension.json`
from `FAMILY_MODULES` in one pass (it is not designed for incremental append);
its own guards (R3-R6) fix the minimum size of any rule-compliant refill:

- `PER_FAMILY = 10` -- every family contributes exactly 10 rows or the
  generator refuses (`family {family!r} yields {n} screened candidates, fewer
  than the 10 the refill takes`).
- `assign_partitions()` cycles `(held-out, development, train)` over the
  families sorted by Mathlib module path, restarting the cycle at `held-out`
  for the NEW family set on every invocation of the generator.
- **R5** refuses a refill that adds fewer than 2 new held-out families.

Detail moved to [`../notes/292-nursery-refill-two.md`](docs/plan/notes/292-nursery-refill-two.md).

**DONE for this dispatch (`nat-stragglers`, 2026-08-29).** Both targets closed.

```
F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0   -- proved
F:ml430-nat-base-induction-83561d4c               -- proved
```

**`add_div_of_dvd_add_add_one`.** `∀ {c a b}, c ∣ (a+b+1) → (a+b)/c = a/c+b/c`.
The prior lane's route sketch (compare divisibility's forced remainder
against a case split on `ra+rb` vs `c`) was directionally right but the
actual derivation needed was cleaner than either sketch or my own first plan:
decompose `a=c*qa+ra`, `b=c*qb+rb` via `div_mod_exec`, so `a+b+1 =
c*(qa+qb)+(ra+rb+1)`. Case-split `ra+rb+1` against `c` (`lt_or_ge`) — below
`c` this is ALREADY a valid `divMod` decomposition of `a+b+1`, and comparing
it against the one the `dvd` witness gives (remainder `0`) via
`div_mod_unique` forces `ra+rb+1=0`, refuted by `succ_ne_zero` since it's a
successor. At or above `c`, subtracting `c` once (`sub_add_cancel`) gives a
remainder `r'` also `<c` (bounded via `ra<c`,`rb<c` and
`le_of_succ_le_succ`/`add_le_add_left`/`add_le_add_right`/`le_trans`), and
comparing THAT decomposition against the same `dvd`-witness relation forces
`r'=0`, i.e. `ra+rb+1=c` exactly — pinning `ra+rb=c-1<c`, which closes the
goal against `div_mod_exec`'s own decomposition of `a+b`. No case-split on
the `dvd` witness `q`'s shape was needed at all (an earlier plan detour I
abandoned once the derivation above worked without it). New file
`nat_prelude/div_mod_lemmas.rs` extension (the ninth/last mirror in that
family); module doc there has the full step list.

Detail moved to [`../notes/293-nat-stragglers.md`](docs/plan/notes/293-nat-stragglers.md).

**Lane block (`DONE -- ADR-0615 accepted, generator fixed, draw 2 landed`,
nursery-ceiling-adr, 2026-08-29).**

## Headline

The ceiling was **not** the blocker, and raising it would have been the wrong
move. The generator had three independent obstacles to a second draw; **two of
them destroy data**, and the ceiling -- the only one anybody had noticed -- was
accidentally shielding the ledger from the other two.

| | before | after |
| --- | --- | --- |
| DISPATCHABLE | 11 | **31** |
| held-out rows / families / split keys | 67 / 5 / 16 | **87 / 7 / 21** |
| quoted cohort | 80 | **120** of a 214 ceiling |
| existing fact files modified by the draw | -- | **0** |

## Step 0 -- re-measurement (main merged, everything re-run)

```
python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 99
  held-out (blind evaluation, do not dispatch): 65
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 11
exit 0

python3 scripts/check-autogenesis-holdout-isolation.py     (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=67|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Every number in the brief reproduced. Populations: `nursery-v1.json` 216 entries
(214 evaluation + 2 longitudinal), `nursery-v2-extension.json` 80, combined 294
against `EVALUATION_CEILING = 300`.

Two brief numbers refined by measurement rather than contradicted:

- **"39 of 50 closed in a few hours"** is exact. 21 development + 18 train of
  the 50 dispatchable v2 rows are `proved`; the refill landed 17:22 and the
  closures run 18:03 -> 19:19.
- The whole-day figure is larger and is the one that should drive sizing:
  **60 `ml430` mirrors flipped to `proved` today** (135 -> 195), the other 21
  coming from the pre-existing v1 backlog.

## The ceiling's origin -- traced, not assumed

`EVALUATION_CEILING = 300` was introduced **this morning** (`94b3e61`,
`feat(autogenesis): the statable-here screen, and an 80-row refill`), and its
comment cites its source honestly rather than inventing a number:

```python
# R3 -- the ceiling. v1's policy caps the evaluation population at 300.
```

That is a faithful transcription of `nursery-v1.json` ->
`policy.evaluation_fact_count` = `{minimum: 100, maximum: 300}`, itself pinned
as a literal in `scripts/check-autogenesis-nursery.py:82` as *"the 100..300
programme range"*. The range enters on **2026-08-18** (`2d65f19d8`,
`c9717b3bc`), with authority **ADR-0478** and roadmap task **AG2.3** -- both of
which state it as a sizing target for a population that was then **empty**.

Detail moved to [`../notes/294-nursery-ceiling-adr.md`](docs/plan/notes/294-nursery-ceiling-adr.md).

**DONE for this dispatch (`totient-even`, 2026-08-29).**

**The task.** Land the two cheap totient mirrors the `totient-counting` lane
left a verified route for, then spend remaining budget on `Nat.totient_even`
(piece 2 of the `nat-totient` triage) — either build it, or produce a
hand-traced, numerically checked plan if a build is not safe to land in the
remaining budget.

## Part 1 — the two mirrors, closed

**`F:ml430-nat-dvd-two-of-totient-le-one-3642bf31`** and
**`F:ml430-nat-totient-eq-one-iff-68d883a0`** are both `proved`,
`proof_route: kernel-lean`, `axiom_footprint: []`. Verified the previous
lane's recorded route by BUILDING it rather than trusting it, and it held
with no case-split-order surprises:

- `Nat.dvd_two_of_totient_le_one` (`0 < a -> totient a <= 1 -> a | 2`):
  `trichotomy` at `c = 2` on `a`. `a < 2` combined with `0 < a` forces
  `a = 1` (`le_of_succ_le_succ` + `le_antisymm`), closed by a concrete `dvd
  1 2` witness (`one_mul` gives `2 = 1*2`). `a = 2` is `dvd_refl`. `2 < a`
  is refuted by the shared core below.
- `Nat.totient_eq_one_iff` (`totient n = 1 <-> n = 1 \/ n = 2`): reverse
  direction is two `def_eq` reductions (`totient 1 = totient 2 = 1`,
  `d.refl` accepted up to defeq). Forward direction shares the same
  `trichotomy` shape: `n < 2` splits again (`lt_or_eq_of_le`) into `n = 0`
  (contradicts `totient n = 1` via `totient 0 = 0` by defeq, refuted by
  `succ_ne_zero`) or `n = 1` (`or_inl`); `n = 2` is `or_inr`; `2 < n` uses
  the same shared refutation.
- Shared core, `totient_le_one_contradiction_above_two` (new,
  `totient_lemmas.rs`): from `Lt two x` and `Le (totient x) one`, derive
  `False` by composing `countRange_ge_two_of_two_witnesses` at witnesses
  `1` (`coprime_one_left_iff`, unconditional) and `pred x`
  (`coprime_succ_self`, after `x = succ (pred x)` via `succ_pred_of_pos`),
  then chaining the resulting `Le two (totient x)` against the hypothesis
  via `le_trans` into the impossible `Le two one`, refuted by peeling two
  `succ`s down to `not_succ_le_zero`.
- New local helper `trichotomy_elim`: a full three-way eliminator for
  `finite::trichotomy` (`Or (Lt x c) (Or (Eq x c) (Lt c x))` directly into a
  proof of one target), generalizing `finite.rs`'s `two_way_split` (which
  only eliminates the middle case). Also `dvd_intro`, a local copy of
  `divisibility.rs`'s private helper of the same name (this file's own
  local-copies-per-file convention).

Detail moved to [`../notes/295-totient-even.md`](docs/plan/notes/295-totient-even.md).

**DONE for this dispatch (`nat-coprime-family`, 2026-08-29).** All nine
target facts closed: `epistemic_status: proved`, `proof_route: kernel-lean`,
`axiom_footprint: []`.

## The task

```
F:ml430-nat-coprime-coprime-div-right-7a8ce438
F:ml430-nat-coprime-coprime-dvd-left-2ce391d2
F:ml430-nat-coprime-coprime-dvd-right-4a2670ae
F:ml430-nat-coprime-coprime-mul-left-fb5bd11a
F:ml430-nat-coprime-coprime-mul-left-right-910d7d8f
F:ml430-nat-coprime-coprime-mul-right-70e4e946
F:ml430-nat-coprime-coprime-mul-right-right-9599ecd3
F:ml430-nat-coprime-dvd-of-dvd-mul-left-b0608cb9
F:ml430-nat-coprime-dvd-of-dvd-mul-right-efc3a4ec
```

All nine mirror `Init.Data.Nat.Coprime` — Lean **core** (not mathlib4
itself). Confirmed by reading the pinned toolchain source directly:
`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Coprime.lean`.
`Nat.Coprime m n := gcd m n = 1` there, matching this prelude's own
convention (`rel_prime.rs`'s module doc: `Coprime` is never given a separate
name here, always spelled `gcd _ _ = one` inline) — so every mirror-flip
here is the honest kind (same definition, not a theorem about a different
one).

## Step 0 — two were already proved

`primes.rs`'s `Nat.coprime_of_dvd_left`/`Nat.coprime_of_dvd_right` (built
for an earlier, differently-named fact) state the IDENTICAL propositions as
`coprime-coprime-dvd-left`/`coprime-coprime-dvd-right` once `Coprime` is
unfolded — checked by comparing argument roles against the doc comment, not
by name. Closed as thin one-line wrappers under the Mathlib name rather than
aliases, to keep the one-fact-one-declaration correspondence the ledger's
checkers lean on.

## The other seven

New file `crates/axeyum-lean-kernel/src/nat_prelude/coprime_lemmas.rs`
(all nine declarations, one dispatcher `declare_coprime_lemmas`, called from
`build_nat_prelude` right after `declare_coprime_of_dvd_both`):

Detail moved to [`../notes/296-nat-coprime-family.md`](docs/plan/notes/296-nat-coprime-family.md).

**Closed all five targets** (`DONE`, nat-mul-order, 2026-08-29): `2f9162c98`.
New file `crates/axeyum-lean-kernel/src/nat_prelude/mul_order_lemmas.rs`
declares `Nat.mul_lt_mul_left`, `Nat.mul_lt_mul_right`,
`Nat.lt_of_mul_lt_mul_left`, `Nat.lt_of_mul_lt_mul_right`,
`Nat.div_lt_of_lt_mul`, dispatched last in `nat_prelude.rs`'s build order.

Step 0 (`nat_theorem_inventory --release`) confirmed all five absent under any
rendered type before writing any proof — no duplicate work.

The two `lt_of_mul_lt_mul_*` cancellation lemmas carry **no** positivity
hypothesis, matching the pinned Mathlib v4.30 source exactly (`a*b < a*c` at
`a = 0` is vacuous, so requiring `0 < a` would only be a weaker true
statement). Proved by contradiction via `lt_or_ge` + `mul_le_mul_left`/
`le_trans`/`lt_irrefl`, no `Nat.rec` case split. `mul_lt_mul_left`/`right` are
the matching `Iff` (`mp` = the cancellation lemma, `mpr` = a positive-monotone
core). `div_lt_of_lt_mul` is the one real case split, on the divisor
(`cases_zero_succ`): `n = 0` is absurd via `zero_mul`/`not_lt_zero`; `n = succ
n'` is `div_mod_lt_mul_iff`'s forward direction fed the `div_mod_exec`
witness.

**One real bug, found by bisection.** A first draft of
`mul_lt_mul_pos_right_core` assumed `mul(succ b, a) = add(mul b a, a)` held BY
REFL — copying the pattern that genuinely does hold in the *left* core
(`mul_succ`, a refl-provable defining equation, since `Nat.mul` recurses on
its right argument). The left-successor form (`succ_mul`) is instead a real
theorem under "multiplicative theorems", proved by induction. This poisoned
the whole prelude build (`TypeMismatch` across all 169 `nat_prelude::` tests);
bisected by toggling the three new `declare_*` dispatch calls one at a time
against `nat_theorem_inventory`, then further by disabling the second
`d.theorem` call inside `declare_mul_lt_mul_iff`. Fixed with an explicit
`transport` along `succ_mul`.

`theorem_names`/`the_build_is_deterministic` pin: `93 + 538` → `93 + 543`
(new value taken from the panic's own mismatch, not hand-incremented). New
test `mul_order_lemmas_apply_at_concrete_and_boundary_instances` applies all
five at concrete numerals, including the boundary `a = 1` (smallest value
satisfying `0 < a`) and `n = 1` (smallest divisor taking the `succ`
case-split branch), plus `7 < 2*4` at the `div_lt_of_lt_mul` boundary.
Confirmed "1 passed", never "0 filtered out".

Detail moved to [`../notes/297-nat-mul-order.md`](docs/plan/notes/297-nat-mul-order.md).

**Done (`DONE`, nat-mod-mul, 2026-08-29).** All five targets closed; none
were already proved under these names (checked `nat_theorem_inventory
--release` before starting -- `mod_mul`, `mod_mul_left_mod`,
`mod_mul_right_mod`, `mod_mul_left_div_self`, `mod_mul_right_div_self` all
came back absent; no existing lemma in `division.rs`/`parity.rs` covered the
same shape either, confirmed by grepping proof bodies for `mod_mod`/`mod_mul`).

New file `crates/axeyum-lean-kernel/src/nat_prelude/mod_mul_lemmas.rs`
(`declare_mod_mul_family`, called right after
`declare_add_div_of_dvd_add_add_one` in `build_nat_prelude`, which sits on the
same dependency set). One reusable helper covered all five:

- `double_decompose(a, pos_a, b, pos_b, x)` reconstructs
  `divMod (a*b) x ((x/a)/b) (x%a + a*(x/a%b))` for positive `a`, `b` from two
  `div_mod_exec` decompositions (`x` at `a`, then `x/a` at `b`), combined via
  `left_distrib`/`mul_assoc`/`add_assoc`/`add_comm`. `mod_mul_eq` compares it
  against the canonical decomposition of `x` at `a*b` via `div_mod_unique` to
  get `Nat.mod_mul` directly (`F:ml430-nat-mod-mul-beaccbad`).
- `mod_of_dvd_mod(dvsr, mult, e, e_eq, a)` is the general "`e` a multiple of
  `dvsr` implies `a % e % dvsr = a % dvsr`" fact, built the same way (a second
  `divMod dvsr a _ rd` decomposition compared via `div_mod_unique`) rather
  than derived from `mod_mul`. Closes `mod_mul_left_mod` and
  `mod_mul_right_mod` (the two differ only in which of `b`/`c` is `dvsr`, and
  whether `e_eq` needs a `mul_comm` bridge or is `refl`).
- `mod_mul_div_self(n, k, m, e, e_eq)` chains `mod_mul_eq` +
  `add_mul_div_left` (already declared, same dispatch batch) + a third local
  helper `div_of_lt` (the generic "a value below the divisor divides to `0`"
  fact) to get `div (mod m e) n = mod (div m n) k`. Closes
  `mod_mul_left_div_self` and `mod_mul_right_div_self`.

Detail moved to [`../notes/298-nat-mod-mul.md`](docs/plan/notes/298-nat-mod-mul.md).

**DONE for this dispatch (`totient-even-exec`, 2026-08-29).**

## The task

Execute `docs/plan/status/295-totient-even.md`'s hand-traced plan for
`Nat.totient_even`. That plan identified one genuinely new piece — a general,
`totient`-independent evenness lemma over `countRange` — and flagged it as
the whole risk, since it was traced without compiling anything. This dispatch
built it, found and fixed the one place the trace didn't hold, and verified
it against the kernel.

## What was built: `Nat.countRange_reversal_even`

```
Nat.countRange_reversal_even :
  forall (L : Nat) (h : Nat -> Bool),
    (forall j, Lt j L -> Eq Bool (h (sub (pred L) j)) (h j)) ->
    (forall j, Lt j L -> Eq Bool (h j) true -> Not (Eq Nat j (sub (pred L) j))) ->
    Even (countRange h L)
```

`L` is bound outermost (not `h` first, as the plan's prose sketch has it) —
an equivalent, differently-curried statement, chosen so `L` is directly the
`WellFounded.fix`-eliminated variable.

New file: `crates/axeyum-lean-kernel/src/nat_prelude/count_range_reversal.rs`
(~890 lines after formatting). Registered in `nat_prelude.rs` (field, doc,
`name_str` constructor, `mod` declaration, dispatch call right after
`declare_parity_all` — see "what did not hold" below for why not right after
`declare_totient_all`). Listed in `nat_prelude_tests.rs`'s `theorem_names`
(the environment-derived coverage assertion, `every_nat_declaration_is_
checked_and_axiom_free`, requires this — it caught the omission on the first
full-suite run). One new concrete-instance test,
`count_range_reversal_even_applies_at_a_vacuous_concrete_instance`.

Nothing in the statement or proof mentions `gcd`/`totient` — it is a pure
counting fact, reusable well beyond this task.

## Which traced steps held, and which didn't

**Held exactly as traced:**

Detail moved to [`../notes/299-totient-even-exec.md`](docs/plan/notes/299-totient-even-exec.md).

**Lane block (`DONE -- draw 3 landed, 40 rows, 2 new held-out families`,
nursery-draw-three, 2026-08-29).**

## Headline

Dispatchable was down to **8** (7 of them one family, mostly blocked on
infrastructure). Draw 3 adds **40 rows across 4 new families** under
ADR-0615's per-cohort envelope. Two of the four are the SAME candidates a
first attempt tried and R9 rejected -- the corrected set below is R9-clean.

| | before | after |
| --- | --- | --- |
| DISPATCHABLE | 8 | **28** |
| held-out rows / families / split keys | 87 / 7 / -- | **107 / 9 / --** |
| quoted cohort | 120 | **160** of a 214 ceiling |
| already-proved fraction of dispatchable | -- | **6/28 (21.4%)** |
| existing fact files modified by the draw | -- | **0** |

## Step 0 -- re-measurement (main merged first: five commits landed in the
hours before this lane started -- coprimality, mul-order, mod-mul families
all closed)

```
python3 scripts/check-dispatchable-frontier.py
  open ml430 mirrors: 99
  held-out: 65   mutation controls: 12   structurally blocked: 11
  DISPATCHABLE: 8
      F:ml430-nat-coprime-coprime-div-left-6f7082bd
      F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      F:ml430-nat-odd-totient-iff-{,eq-one-}{b6a6596f,d0491d84}
      F:ml430-nat-totient-{coprime-totient-iff,dvd-of-dvd,even,gcd-mul-totient-mul}-*

python3 scripts/check-autogenesis-holdout-isolation.py     (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=87|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Headroom, re-derived from the generator's own constants, not from the brief's
arithmetic: `V1_EVALUATION_ENTRIES = 214` (asserted, matches `nursery-v1.json`'s
214 evaluation entries + 2 longitudinal = 216 total). `nursery-v2-extension.json`
carried **120** entries before this draw, so headroom was **94 rows**, not the
96 the brief quoted (216 − 120, using the 216 total-file figure rather than the
214-evaluation figure the ceiling actually governs). A 40-row draw fits either
way with room to spare.

## Family selection -- two rounds, because the first round was wrong

Detail moved to [`../notes/300-nursery-draw-three.md`](docs/plan/notes/300-nursery-draw-three.md).

**DONE for this dispatch (`totient-multiplicative`, 2026-08-29).**

## Part 1 — the quick one, closed

**`F:ml430-nat-coprime-coprime-div-left-6f7082bd`** is `proved`,
`proof_route: kernel-lean`, `axiom_footprint: []`. `Nat.coprime_div_left`
(`nat_prelude/coprime_lemmas.rs::declare_coprime_div_left`) is the exact
mirror image of the already-closed `Nat.coprime_div_right`: the divided
argument moves from `n` to `m`, and the succ-branch shrink step uses
`coprime_of_dvd_left` (shrinking the LEFT `gcd` argument) instead of
`coprime_of_dvd_right`. (Lean core actually proves `coprime_div_right` FROM
`coprime_div_left` via `.symm` — this kernel has no `gcd_comm` at the time
this mirror was built, so it went the other way, building `coprime_div_left`
directly instead of transporting through `.symm`; see Part 2 below, which
lands `gcd_comm` anyway for unrelated reasons.) Pinned by a
concrete-instantiation test exercising both branches
(`coprime_div_left_applies_at_both_branches_of_its_case_split`), checking the
residue lands in the FIRST argument (`Coprime (div 10 2) 3`, not `Coprime 3
(div 10 2)`).

`depends_on` completed via `scripts/check-fact-depends-derived.py`
(`missing_edges=0`). Both evidence `checker_command`s verified to pass on the
real name (count 1) and fail on a fabricated one (count 0, exit 1).

## Part 2 — `Nat.gcd_comm`, landed as unplanned but necessary infrastructure

Detail moved to [`../notes/301-totient-multiplicative.md`](docs/plan/notes/301-totient-multiplicative.md).

**Lane block (`DONE -- 23 facts repaired, gate registered in both aggregate
gates, 9 guards each mutation-verified`, mirror-statement-repair, 2026-08-29).**

## Headline

| | before | after |
| --- | --- | --- |
| `ml430` mirrors whose `formal.statement` is a kernel rendering | 19 | **0** |
| `ml430` mirrors whose statement matches its preregistered hash | 358 / 362 | **362 / 362** |
| gate detecting either | none | `check-mirror-statement-fidelity.py`, both gates |
| guards, each killed by exactly one control | -- | **9 / 9** |
| false-positive controls | -- | 4 (one over the real ledger) |

The reported 19 is exact and reproduces. The restore source is **not** the
nursery manifest the brief and the design review both expected -- it is a
**content hash**, which makes the repair verifiable rather than merely
corroborated.

## Step 0 -- re-measurement, reproduced then widened

```
total facts 2114 | ml430 374 | non-ml430 1740
  starts-theorem   19        x0-binder  18        Eq.{  13
  AxNat            19        ascii-arrow 18
union flagged by ANY of twelve signatures: 19
baseline signature (starts-`theorem ` | AxNat | AxInt): 19
EXTRA beyond baseline: 0
```

I widened the detector to twelve independent kernel-rendering signatures --
`AxRat`, `AxReal`, `CReal`, `Eq.{`, an `(xN :` binder, a leading `def `/
`axiom `, `Sort.{`/`Type.{`, an ASCII ` -> ` arrow -- and **the union is the
same 19 files.** No twentieth fact exists under any wider signature.

**Positive control.** The 355 unflagged mirrors carry Mathlib surface syntax
(`∀ (a b c : ℤ), a + b + c = a + (b + c)`), so the detector is not flagging
everything.

Two sub-signatures are individually INCOMPLETE and each would have missed
`Nat.not_coprime_zero_zero`, which is a closed statement and therefore has
neither a binder nor an arrow. Only `starts-theorem ` and `AxNat` are complete
over this set -- which is the reviewer's original pair, arrived at
independently.

## The restore source: a preregistered HASH, not a transcription

`artifacts/autogenesis/nursery-v*.json` does **not** hold a pinned `type` per
row. Its entries are `fact_id` / `partition` / `family` / `proof_shape` /
`provenance_class` and nothing else. Following the brief literally would have
found nothing.

What does exist is better. `artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json`
(and `nursery-v2-extension.json` for the later draws) pins
`source_statement_sha256` per fact -- a **SHA-256 of the Mathlib statement
text**. So the check is cryptographic:

```
sha256(creating-commit `formal.statement`) == preregistered source_statement_sha256
   ->  19 of 19
```

Detail moved to [`../notes/302-mirror-statement-repair.md`](docs/plan/notes/302-mirror-statement-repair.md).

**DONE for this dispatch (`int-add-basics`, 2026-08-29).**

## Task

Close nine `ml430` mirror facts for basic `Int` addition algebra:
`add_comm`, `add_left_cancel`, `add_left_comm`, `add_left_inj`, `add_left_neg`,
`add_mul`, `add_neg_cancel_left`, `add_neg_cancel_right`, `add_neg_eq_sub`.

## What already existed vs. what was built

Checked the full `Int` inventory first (`int_theorem_inventory`, no filter —
this example builds the whole `Int` prelude by default, no
`--include-constructed` flag needed or supported): 201 theorems, 0 asserted,
before this lane touched anything.

**Two of the nine already existed**, matched by rendered kernel type against
each fact's `formal.statement`, not by name:

- `Int.add_comm` — `algebra.rs`, exact match for `a + b = b + a`.
- `Int.add_neg_cancel_right` — `algebra.rs`, exact match for
  `a + b + -b = a`.

**The other seven did not exist** (confirmed absent by grepping the full
inventory for `add_left_*`, `add_mul`, `neg_eq_sub`, `neg_cancel_left` — none
present under any name), and were built in a new file,
`crates/axeyum-lean-kernel/src/int_prelude/add_basics.rs`:

Detail moved to [`../notes/303-int-add-basics.md`](docs/plan/notes/303-int-add-basics.md).

**Lane block (`DONE -- 10/10 facts closed, 173/173 nat_prelude:: tests green`,
nat-add-basics, 2026-08-29).**

## Headline

| fact | route |
| --- | --- |
| `F:ml430-nat-add-assoc-8c87a1f1` | already existed (`Nat.add_assoc`, `algebra.rs`) -- evidence only |
| `F:ml430-nat-add-comm-56a2d614` | already existed (`Nat.add_comm`, `algebra.rs`) -- evidence only |
| `F:ml430-nat-add-add-add-comm-74d2c151` | new: `Nat.add_add_add_comm` |
| `F:ml430-nat-add-eq-ab0eab69` | new: `Nat.add_eq` (`Eq.refl`, see below) |
| `F:ml430-nat-add-eq-left-8e12789f` | new: `Nat.add_eq_left` |
| `F:ml430-nat-add-eq-right-9067eb1a` | new: `Nat.add_eq_right` |
| `F:ml430-nat-add-eq-zero-64233539` | new: `Nat.add_eq_zero_iff` (NOT `add_eq_zero` -- see below) |
| `F:ml430-nat-add-eq-one-iff-f8463abc` | new: `Nat.add_eq_one_iff`, shared helper |
| `F:ml430-nat-add-eq-two-iff-25385c65` | new: `Nat.add_eq_two_iff`, shared helper |
| `F:ml430-nat-add-eq-three-iff-799a0a8f` | new: `Nat.add_eq_three_iff`, shared helper |

All 10 facts now `epistemic_status: proved`, `python3 scripts/validate-facts.py`
reports 0 errors, `python3 scripts/check-fact-depends-derived.py --fix` ran
(added 180 edges across 128 facts ledger-wide -- flipping `add_assoc`/`add_comm`
from open to proved surfaced every OTHER already-proved fact whose proof term
uses them and had no `depends_on` edge yet, not just this lane's new facts).

## Which already existed

Checked first against `nat_theorem_inventory --release`, comparing rendered
type to `formal.statement`, per the brief:

- `Nat.add_assoc` and `Nat.add_comm` were already declared verbatim in
  `nat_prelude/algebra.rs`'s `declare_additive_theorems`, predating this
  session. Closed by evidence pointing at the existing declaration -- no new
  proof code.
- `Nat.add_eq_zero` ALSO already existed (`declare_add_no_zero_summands`,
  built earlier for a bitwise `land_aux`/`lor_aux` zero-summand argument), but
  its type is the WEAKER mp-only arrow `add a b = 0 -> a = 0 /\ b = 0`, not
  the `Iff` this fact's `formal.statement` states. Read Mathlib's actual
  source (`Init/Data/Nat/Lemmas.lean` at the pinned commit `c5ea0035…`):
  `Nat.add_eq_zero` there is a `@[deprecated Nat.add_eq_zero_iff (since :=
  "2025-10-26")]` alias for the SAME `Iff`. A prelude can never redeclare a
  taken name, so the new `Iff` theorem is named `Nat.add_eq_zero_iff` (the
  post-rename Mathlib name) rather than colliding with the existing weaker
  arrow. mp reuses the existing `add_eq_zero` directly; mpr is new.

## The `add_eq_{one,two,three}_iff` group -- one shared helper

Detail moved to [`../notes/304-nat-add-basics.md`](docs/plan/notes/304-nat-add-basics.md).

**Lane block (`DONE -- 159 of 160 attested, 1 rejected and recorded`,
lean-attestation-s5, 2026-08-29).**

## Headline

**s5 can do it, and it is cheap: 3.6 s for all 160 rows.** Three lanes today
worked around a missing Mathlib by inventing a weaker, labelled *quotation*
grade. That grade was honest and it was also unnecessary on this fleet.

| | before | after |
| --- | --- | --- |
| extension rows carrying a real Lean attestation | 0 | **159** of 160 |
| rows Lean REJECTS | unknown | **1**, recorded |
| grade | flat literal `"quotation"` | derived per row from the run |
| facts asserting a now-false quotation claim | 35 | **0** |
| new artifacts under `artifacts/autogenesis/` | -- | **0** (folded into the manifest) |

The row count is **160**, not the 120 the brief said: a third draw landed 40
more rows the same day.

## 1. Can s5 do it? Yes, end to end

Verified by elaborating, not by listing a build directory.

```
host            s5   (ssh BatchMode, 16 c, 27 G)
mathlib         ~/lean-import-scale/mathlib4   c5ea00351c28f...  .lake/build 6.2 GB
lean            4.30.0  d024af099ca4bf2c86f649261ebf59565dc8c622
import Mathlib + 160 proof-free axioms  ->  3.6 s
negative control                        ->  REJECTED (good)
```

The checkout's 64 `git status` entries are all **untracked probe `.lean` files**
from earlier lanes. No tracked file is modified and the commit is the one we
pin, so the checkout is trustworthy.

## 2. The finding: `Nat.le_induction` is not a well-formed proposition

**159 of 160 elaborate. One does not.**

```
F:ml430-nat-le-induction-2f088ac3   Nat.le_induction
family natural-induction-and-divisibility   partition HELD-OUT

  ∀ {m : ℕ} {P : (n : ℕ) → m ≤ n → Prop},
    P m ⋯ → (∀ (n : ℕ) (hmn : m ≤ n), P n hmn → P (n + 1) ⋯)
          → ∀ (n : ℕ) (hmn : m ≤ n), P n hmn

  error: don't know how to synthesize placeholder   ⊢ m ≤ m
  error: don't know how to synthesize placeholder   ⊢ m ≤ n + 1
```

`⋯` is Lean's pretty-printer glyph for an **elided proof term** (here `m.le_refl`
and `le_succ_of_le hn`). Re-parsed it is a hole Lean cannot fill. So we
preregistered a string that is not a proposition, and it **can never be closed
as stated**.

This is precisely the risk the quotation grade named and structurally could not
detect — *"a pretty-printed type is not guaranteed to re-parse"* — and the
per-row `source_statement_sha256` cannot see it either, because the checksum
faithfully binds a **lossy** string. Only elaboration distinguishes them.

**Confirmed in both directions**, because a parse error can desync Lean's parser
and swallow following lines:

Detail moved to [`../notes/305-lean-attestation-s5.md`](docs/plan/notes/305-lean-attestation-s5.md).

**DONE for this dispatch (`totient-even-finish`, 2026-08-29).**

## The task

Finish `Nat.totient_even` from `docs/plan/status/299-totient-even-exec.md`'s
verified general lemma (`Nat.countRange_reversal_even`), then land the three
mirrors it unblocks per `totient_lemmas.rs`'s module doc:

```
F:ml430-nat-totient-even-28e0415f
F:ml430-nat-odd-totient-iff-b6a6596f
F:ml430-nat-odd-totient-iff-eq-one-d0491d84
F:ml430-nat-totient-coprime-totient-iff-3932cf83   (half)
```

## Result: three of four closed, one left open with a concrete plan

- **`F:ml430-nat-totient-even-28e0415f`** — `proved`, `kernel-lean`,
  `axiom_footprint: []`.
- **`F:ml430-nat-odd-totient-iff-eq-one-d0491d84`** — `proved`, same route
  class.
- **`F:ml430-nat-odd-totient-iff-b6a6596f`** — `proved`, same route class.
- **`F:ml430-nat-totient-coprime-totient-iff-3932cf83`** — still `open`. See
  "What's left" below; the plan is concrete but was not attempted this
  session (budget).

## `Nat.totient_even` — the bug the exec lane's build could not have caught

The general lemma `Nat.countRange_reversal_even` (`count_range_reversal.rs`,
landed by `totient-even-exec`) needed no changes. Wiring it to `totient`
needed:

Detail moved to [`../notes/306-totient-even-finish.md`](docs/plan/notes/306-totient-even-finish.md).

**Lane block (`DONE -- tool, nine mutation-verified controls, and `just brief``,
brief-step0, 2026-08-29).**

## Headline

`scripts/brief-step0.py` produces the evidence a brief should *contain* rather
than *ask for*, in **0.2-0.5 s** against a warm snapshot. `just brief <targets>`
is the loop-closing mechanism, and §6 argues why a gate was **not** the right
answer here.

On its first real use it found **14 of 141 open facts whose statement already
has an exact-constant match in the kernel environment** -- including
`F:ml430-nat-dvd-antisymm-507f9026`, which is `open` while `Nat.dvd_antisymm` is
proved at precisely its statement.

## 1. The two numbers, re-measured before anything was built on them

| practice | docs | of 272 | pct |
| --- | --- | --- | --- |
| mutation testing (`mutation`/`mutant`, case-insensitive) | 125 | 272 | **46.0%** |
| `shape_search` / `shape-search` | 13 | 272 | **4.8%** |

```
/usr/bin/grep -lEi 'mutation|mutant' docs/plan/status/*.md | wc -l        -> 125
/usr/bin/grep -lE  'shape_search|shape-search' docs/plan/status/*.md | wc -l -> 13
ls docs/plan/status/*.md | wc -l                                          -> 272
```

GNU grep at `/usr/bin/grep`, not the interactive `ugrep` shell function.
Positive control: `/usr/bin/grep -lE '[a-z]' docs/plan/status/*.md | wc -l` →
**272** -- the query reaches every document, so a zero would have meant
something. Negative control: a fabricated token → **0**.

The retrospective measured 269 documents; three landed since. Both percentages
are unchanged to one decimal place. **Compliance tracks mechanization, not
emphasis** survives re-measurement.

## 2. What the tool reports

Four sections per target, plain text, pasteable into a brief.

**1 -- Does it already exist?** Every declaration in a kernel-built snapshot is
ranked by the **multiset of constants in its RENDERED TYPE** against the fact's
`formal.statement`. Names are never compared: a name search cannot find a lemma
whose name you do not know, which is the case that has cost the work. Carrier
and sort tokens are held out of the multiset and compared separately, because a
rendered type spells the carrier once per binder *and* once per `Eq.{1}`
argument while a surface statement spells it once per binder group.

It separates propositions a name search cannot:

```
F:ml430-nat-add-eq-zero-64233539   ∀ {m n : ℕ}, m + n = 0 ↔ m = 0 ∧ n = 0
  [1.00] Nat.add_eq_zero_iff   … Iff (Eq (add x0 x1) zero) (And (Eq x0 zero) (Eq x1 zero))
  [0.89] Nat.add_eq_zero       … (Eq (add x0 x1) zero) -> And (Eq x0 zero) (Eq x1 zero)
```

Detail moved to [`../notes/307-brief-step0.md`](docs/plan/notes/307-brief-step0.md).

**Your lane's block (`DONE for this pass`, orphan-script-audit, 2026-08-29).**
Re-measured the 2026-08-29 process retrospective's "352 of 503" orphan-script
claim from scratch, found the correct number (349 of 504, reproducing the
retrospective within corpus drift), diagnosed why an independent cruder query
landed at 398, archived the 346 dead one-off capsule checkers plus their 92
orphan controls, registered the 3 genuinely useful never-wired-up scripts as
new gate steps, and repaired the opt-out fallout the archival caused. Nothing
left half-done; no further action required from the next lane on this
specific audit, though the retrospective's suggested "subject registration"
ratchet (mirroring `check-control-registration.sh` for `check-*` SUBJECTS,
not just their controls) remains unbuilt — see "Left for later" below.

## The census: method, numbers, and why they disagree

**Universe.** `scripts/check-*.{sh,py}` at the top level of `scripts/` (not
recursive — nothing matching lives in a subdirectory): **504** files. (The
retrospective's snapshot was 503; two scripts — `check-fast.sh`,
`check-mirror-statement-fidelity.py` — landed between its snapshot and this
one, both live.)

**Method.** A file X "references" script Y if Y's basename (or, for
`scripts/tests/test_*.py`, its dotted-module form `scripts.tests.NAME` too —
see below) is a substring of X's text. Roots: `scripts/check.sh`, `justfile`,
`hooks/*`, `.github/workflows/*`, and every `artifacts/facts/*.json`
`checker_command`. Compute the full reference graph over every file under
`scripts/` (not just `check-*` ones — an intermediate helper like
`run-python-controls.py` can itself be named by a root and then name further
scripts), BFS from the roots, and a `check-*` script is LIVE iff it is in the
closure. Two built-in controls run every time: **positive** —
`check-aggregate-scope.sh` must classify as live (it does); **negative** — a
fabricated name `check-zzz-nonexistent.sh` must get zero hits anywhere (it
does).

**Three numbers, and only one survives scrutiny:**

Detail moved to [`../notes/308-orphan-script-audit.md`](docs/plan/notes/308-orphan-script-audit.md).

**Lane block (`DONE -- draw 4 landed, 40 rows, attested, 2 new held-out
rows found unclosable`, nursery-draw-four, 2026-08-29).**

## Headline

Dispatchable was down to **8** (7 of them the totient family a sibling lane
was actively closing). Draw 4 adds **40 rows across 4 new families** under
ADR-0615's per-cohort envelope, attests the whole 200-row manifest on s5, and
adds a new S6 screen (`check-dispatchable-frontier.py --statable`) that
rejects a candidate whose statement carries an elided-proof/hygiene glyph
before it can ever be preregistered.

| | before | after |
| --- | --- | --- |
| DISPATCHABLE | 8 | **28** |
| held-out rows / families | 107 / 12 | **127 / 14** |
| quoted cohort | 160 | **200** of 214 ceiling (14 headroom left) |
| already-proved fraction of new dispatchable rows | -- | **10/28 (35.7%)** |
| rows attested on s5 (real Lean, not quotation) | 160/160 (159 elaborate) | **200/200 (197 elaborate)** |
| new NOT-elaborable rows found this draw | -- | **2**, both `integer-absolute-value` |

## Step 0 -- re-measurement

```
python3 scripts/check-dispatchable-frontier.py   (BEFORE)
  open ml430 mirrors: 136
  held-out: 105   mutation controls: 12   structurally blocked: 11
  DISPATCHABLE: 8
      F:ml430-int-add-assoc-749cb0ff
      F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
      F:ml430-nat-odd-totient-iff-{,eq-one-}{b6a6596f,d0491d84}
      F:ml430-nat-totient-{coprime-totient-iff,dvd-of-dvd,even,gcd-mul-totient-mul}-*

python3 scripts/check-autogenesis-holdout-isolation.py   (BEFORE)
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=107|files_scanned=1105|settled=0|references=0|verdict=PASS
```

Headroom, re-derived from `gen-autogenesis-nursery-refill.py --check` rather
than the brief's number (which said 56): `entries=160`, `EXTENSION_CEILING =
V1_EVALUATION_ENTRIES = 214`, so headroom was **54 rows**, not 56. A 40-row
draw fits either way.

## The S6 glyph screen (committed first, before the draw itself)

`docs/contributor-guide/lean-surface-attestation.md` and
`305-lean-attestation-s5.md` asked for exactly this: "screen for `⋯`/`✝` at
extraction, before anything enters your manifest. Nothing does that today."

Added to `scripts/check-dispatchable-frontier.py`'s `--statable` screen as
**S6**: reject a candidate whose statement carries `⋯` (U+22EF), `✝`
(U+271D), `…` (U+2026), or the word `sorry`. The one already-recorded row
(`F:ml430-nat-le-induction-2f088ac3`) is exempted by an explicit, narrow
`KNOWN_GLYPHED_FACT_IDS` allowlist keyed on its exact `fact_id` -- not a
general rule -- per ADR-0615 (never rewrite or delete a preregistered row).

Detail moved to [`../notes/309-nursery-draw-four.md`](docs/plan/notes/309-nursery-draw-four.md).

**Lane block (`DONE -- 21 of 25 exact-constant candidates closed, 4 false
positives correctly left open, already-proved-sweep, 2026-08-29).**

## Headline

Re-ran `scripts/brief-step0.py`'s constant-multiset ranker over the merged
tree (the frontier had moved from the 141 open facts in the tool's own
landing report to **181** open facts with a `formal.statement`, after a
40-row draw landed) and got **25 exact-constant (score >= 0.999) candidates**,
not 14. Reading each one's rendered type character-by-character against the
fact's `formal.statement` -- the tool's own documented limit is that a
constant multiset cannot see argument order -- **21 survive and 4 are false
positives**. Commit: `92a61164eb317e34f7bf25c9a4c90c09c6b7694f`.

## 1. The re-run

```
python3 scripts/brief-step0.py --self-check
  -> SNAPSHOT EXACT, kernel_tree=e8d09cfefeea, declarations=2286
```

The snapshot's tree matched `HEAD:crates/axeyum-lean-kernel` exactly (clean
worktree, freshly merged `main`), so no `--refresh` was needed. Ranking all
181 open `formal.statement`-carrying facts against it (via the module's own
`rank`/`statement_bag` functions, imported directly -- no reimplementation):

| score band | count |
| --- | --- |
| >= 0.999 (exact constant multiset) | **25** |
| 0.75 - 0.999 | 7 |

`scripts/check-autogenesis-already-proved.py` no longer lives at that path --
the same merge that landed `brief-step0.py` also landed a census that archived
346 `check-*` scripts with no live caller
(`98d17aeef`), and this one moved to `scripts/archive/` with a relative-path
bug (`ROOT = parents[1]` now resolves to `scripts/`, one level too shallow,
and its internal call to `check-dispatchable-frontier.py` compounds it to
`scripts/scripts/...`). Ran it from a scratch copy with `ROOT` hardcoded to
this worktree; it independently confirmed **10 of 28** dispatchable rows
name-matched -- a subset of the 21 below. This script answers a narrower
question (name match only) and is now superseded by `brief-step0.py`'s
type-comparing ranker; it is not proposed for un-archiving.

## 2. The 4 false positives -- same constants, different proposition

Detail moved to [`../notes/310-already-proved-sweep.md`](docs/plan/notes/310-already-proved-sweep.md).

**DONE (`int-sign-product`, 2026-08-30).** Closed all five assigned facts:
`Int.mul_pos_iff`, `Int.mul_neg_iff`, `Int.mul_nonneg_iff`, `Int.mul_nonpos_iff`,
`Int.mul_nonneg_of_nonneg_or_nonpos`. New file
`crates/axeyum-lean-kernel/src/int_prelude/sign_product.rs`: one shared sign
case-split (`Int.le_total zero a` / `Int.le_total zero b`) plus six quadrant
facts (two already existed as `Int.mul_nonneg`/`Int.mul_pos`; the other four
built from a sign-flip helper, `neg_mul_neg` reusing `gcd.rs`'s
`neg_mul`/`neg_neg`, and `mul_le_mul_of_nonneg_left` at `c := 0`). All five
are `Theorem`s with empty `axiom_footprint`; `integer` prelude trusted surface
stays 0. `int_prelude::` sweep: 49 passed, 0 failed (was 44 before this lane's
5 additions). `derived_laws` pin recounted 187 -> 192 via
`scripts/recount-pinned-inventory.py`. `clippy -D warnings` clean,
`rustfmt --edition 2024` applied. Facts flipped `open` -> `proved`,
`depends_on` populated by `check-fact-depends-derived.py --fix` (66 edges),
`validate-facts.py` 0 errors, `check-mirror-statement-fidelity.py` PASS. Did
not run the full workspace gate (`just check`/`./scripts/check.sh`) —
scoped to the `int_prelude::` sweep, clippy, fmt and the fact-ledger
validators per the task brief.

Nothing blocked. No follow-up known for this specific family.

**Closed all five dispatched facts** (`DONE`, int-order-coercion, 2026-08-30).

## Step 0 finding: none already existed

`python3 scripts/brief-step0.py` (after a `--refresh --build` — the shared
snapshot was 41.9h stale against the current kernel tree) reported all five
targets `ABSENT` at >=0.75. `Int.le.elim`/`Int.lt.elim` scored high false
positives against `Nat.le_intro` (constant-multiset collision, no argument
order) — read, and confirmed genuinely absent by shape as well
(`shape_search --concl P --hyp Int.le --hyp Eq` came back `UNANSWERABLE`
because `P` is not itself a declared name; the CPS shape has no name to
search for and none was found by grep across `order.rs`).

## What was already there: `le_dest`/`lt_dest`

`Int.le_dest : le a b → ∃ i, b = a + ofNat i` and
`Int.lt_dest : lt a b → ∃ i, b = a + ofNat (i+1)` already existed
(`int_prelude/order.rs::declare_difference_lemmas`, both tracked as their own
proved facts, `F:int-le-dest` / `F:int-lt-dest`). Mathlib's `Int.le.elim` /
`Int.lt.elim` are the CPS elimination form of exactly this existential —
**the brief's "does not exist" call for `le_elim`/`lt_elim` was right about
the CPS shape and wrong to imply nothing related existed**: the
`Exists`-flavoured cousin was sitting right there and the whole task reduced
to `Exists.elim` plus one `isymm` to flip the equation's direction (Mathlib:
`a + n = b`; `le_dest`/`lt_dest`: `b = a + n`).

## `crates/axeyum-lean-kernel/src/int_prelude/order_coercion.rs` (new)

- `Int.le_of_ofNat_le_ofNat` / `Int.lt_of_ofNat_lt_ofNat` — **purely
  definitional, no lemma needed**. `Int.le`/`Int.lt` are `define_binary_int`
  (`defs.rs`), whose `ofNat`/`ofNat` branch is literally `NatOps::le`/
  `NatOps::lt` on the two `Nat` fields, so `Int.le (ofNat m) (ofNat n)` is
  definitionally `Nat.le m n`. The proof is the hypothesis itself; the
  kernel's own defeq check bridges the two sides.
- `Int.le.elim` / `Int.lt.elim` — built via `ops::exists_elim` over
  `le_dest`/`lt_dest`'s witness. The predicate lambda is re-derived locally
  (matching `order.rs`'s private `shift_predicate` exactly) rather than
  widening that module's visibility for one caller — the same choice
  `euclid.rs::declare_decomposition` already makes for the same reason.
  `Int.le.elim`/`Int.lt.elim` are declared as children of `le`/`lt`
  themselves (`kernel.name_str(le_name, "elim")`), the same namespacing
  `Nat.le.step` uses under an unrelated head — required computing `le`/`lt`'s
  `NameId`s as locals in `intern_names` before the struct literal, since two
  fields now need to be children of them.

Detail moved to [`../notes/312-int-order-coercion.md`](docs/plan/notes/312-int-order-coercion.md).

**DONE for this dispatch (`totient-mult-finish`, 2026-08-30).**

## The task

Close `F:ml430-nat-totient-coprime-totient-iff-3932cf83` (the cheap one, per
`306-totient-even-finish.md`'s traced route) and then land one of the two
weakest steps toward `totient(m*n) = totient(m)*totient(n)` per
`301-totient-multiplicative.md`, needed by the remaining three:

```
F:ml430-nat-totient-dvd-of-dvd-9622e44a
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7
```

## Result: `totient_coprime_totient_iff` proved, `coprime_mul_of_coprime` landed, the other three still open

Detail moved to [`../notes/313-totient-mult-finish.md`](docs/plan/notes/313-totient-mult-finish.md).

**Your lane's block (`DONE (prove_mul landed with one reconstructed
certificate; kernel-reconstructed 8 → 9; the "8 more geometry certificates"
sizing is CORRECTED to 3 — five of the eight also need the fractional literal
cast, including the one lane 277 named as cheapest)`, cas-prove-mul,
2026-08-29).**

## Step 0: re-measured before building on it

`python3 scripts/validate-facts.py` at lane start:

    2154 facts checked, 0 errors
    cas-certificate: 36 total -- kernel-reconstructed 8, cas-internal 28

Unchanged from `docs/plan/status/277-cas-multivariate.md`. That lane's arity
survey re-verified against `artifacts/geometry-certificates/` and reproduces
exactly (arities 6–19; `varignon` and `thales` vacuous).

`scripts/brief-step0.py` was not run against a kernel-declaration target: this
lane declares no library lemma. Its subject is one `Check.*` theorem built
inside a `#[cfg(test)]` module, which no environment projection carries, and the
Rust helpers it needed (`prove_merge`, `poly_expr`, `int_poly`) were located by
reading the sibling module directly rather than by name search. The
retrieval-hazard rule still applied and paid: **nine helpers were reused from
`cas_geometry_bridge_tests.rs` by widening them to `pub(super)`, not
re-derived** — including `prove_merge`, which `prove_mul` calls at every
insertion point and which would have been the single largest piece of
duplicated work.

## The correction: `prove_mul` unblocks THREE certificates, not eight

Lane 277 sized "geometry, non-constant cofactors" at **8**, and separately
listed `medians-concurrent` as the one blocked on a fractional-literal cast.
Measured per certificate — counting terms whose serialised `coefficient`
denominator is not `1` — the two blockers **overlap on three of the eight**:

Detail moved to [`../notes/314-cas-prove-mul.md`](docs/plan/notes/314-cas-prove-mul.md).

**Lane block (`DONE -- ADR-0616 accepted, R3 counts by attestation, manifest no
longer contradicts itself`, attestation-ceiling, 2026-08-30).**

## Headline

The promotion is right, and the reason is narrower than "the two cohorts are the
same". **On the STATEMENT an attested extension row is v1's grade and slightly
better-evidenced. On the ROW it is not, and that difference is not repaired by
attestation and is not promoted here.** ADR-0615's exit works once R3 stops
counting manifest membership.

| | before | after |
| --- | --- | --- |
| R3 compares | `len(entries)` vs 214 | unattested vs attested |
| attested cohort | not counted at all | **411** (v1 214 + 197 accepted) |
| unattested cohort | not counted at all | **3** (the rows Lean refused) |
| headroom in rows | **14** | **408** |
| manifest limitations | asserted quotation grade beside a 197-row `attested` list | derived from the run |
| DISPATCHABLE | 8 | 8 (unchanged -- no draw here) |

## Step 0 -- re-measurement (main merged, everything re-run)

```
python3 scripts/gen-autogenesis-nursery-refill.py --check
AUTOGENESIS_NURSERY_REFILL_OK|entries=200|settled_mirrors_admitted=162|bridge=70
  |env=2207|development=60|held-out=90|train=50|combined=414          exit 0

python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 146 | held-out 115 | mutation controls 12
  | structurally blocked 11 | DISPATCHABLE 8                          exit 0
```

Every number in the brief reproduced: 200 entries, `grade =
real-lean-axiom-elaboration-per-row`, `attested` 197, `not_elaborable` 3,
`unattested` 0, 14 rows of headroom against a 40-row minimum draw, queue at 8.

## What the ceiling protects

ADR-0615's rule, quoted from the ADR: *"the unattested cohort may never outweigh
the attested one, which is ADR-0601's 'imports are labeled scaffolding, never
headline' applied to the same distinction."*

So it is a **statement-provenance** rule. It protects the population we measure
ourselves against from being predominantly strings nobody has confirmed are
Mathlib propositions -- the failure the `Nat.le_induction` row is: a
pretty-printed type carrying an elided-proof glyph, preregistered as a
proposition, and not one.

It is **not** a split-integrity rule. Blindness is governed by R1, R8, R9 and
`check-autogenesis-holdout-isolation.py`, per row and per family. Conflating the
two is what made this decision look harder than it is.

## Is an attested extension row the same grade as a v1 row?

Detail moved to [`../notes/315-attestation-ceiling.md`](docs/plan/notes/315-attestation-ceiling.md).

**DONE for this dispatch (`queue-sweep`, 2026-08-30). No fact closed. No
Rust changed.** This lane's value is a correction that stops a future lane
from trying to prove a false lemma, plus a documented reason for declining
all three assigned targets.

## The task

`scripts/check-dispatchable-frontier.py` listed 8 dispatchable facts. Five
are the `Int.mul_*_iff` sign family, explicitly assigned to the sibling lane
`int-sign-product` and skipped here. The remaining three, all `Nat.totient`
statements over general (not-necessarily-coprime) arguments:

```
F:ml430-nat-totient-dvd-of-dvd-9622e44a            a ∣ b → totient a ∣ totient b
F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7   totient(gcd a b) * totient(a*b)
                                                    = totient a * totient b * gcd a b
F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7  a∣b → totient a = totient b
                                                    → a=b ∨ 2*a=b
```

`scripts/brief-step0.py` on each: ABSENT (provisional, stale snapshot; a
fresh `shape_search --concl Or --hyp Nat.dvd --hyp Eq` confirms ABSENT
directly against 1,112 declarations). `scripts/check-autogenesis-already-proved.py`
was also run; it does not name-match any of the three (expected — none is a
verbatim rename of an existing declaration).

## Why these are open, per two prior dedicated lanes

Detail moved to [`../notes/316-queue-sweep.md`](docs/plan/notes/316-queue-sweep.md).

**Your lane's block (`DONE (fractional cast landed; kernel-reconstructed 9 →
10; medians-concurrent reconstructed; centroid-divides-medians and
parallelogram-diagonals-bisect still need prove_mul ON TOP of this cast;
F:cas-partial-fractions-mixed-general-case untouched -- cast-only, next
lane's cheapest target)`, cas-fractional-cast, 2026-08-30).**

## Step 0: re-verified before building

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 37 total -- kernel-reconstructed 9, cas-internal 28

Matches `docs/plan/status/314-cas-prove-mul.md` exactly. Re-verified that
lane's specific correction before starting: `parallelogram-diagonals-bisect`
(lane 277's originally-named "cheapest next target") is genuinely NOT
reachable by the fractional cast alone — every one of its cofactors and both
of its conclusions carry `±1/2`, which is a NON-CONSTANT-cofactor shape
needing `prove_mul` as well. `medians-concurrent` is the one certificate
whose cofactors are constant (`-1`, `-1`) and whose generators are the ones
needing the cast, so it is reachable by the cast alone — confirmed by reading
`artifacts/geometry-certificates/medians-concurrent.json` directly before
writing any Rust.

`scripts/brief-step0.py` was not run against a kernel-declaration target, for
the same reason lane cas-prove-mul's did not: this lane declares no library
lemma, only a `Check.*` theorem inside a `#[cfg(test)]` module.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_frac_bridge_tests.rs`
(new, 3 tests). Two existing helpers widened to `pub(super)` for reuse
(`nat_le_lit` in `cas_ivt_bridge_tests.rs`, `add_left_comm` in
`cas_geometry_bridge_tests.rs`); no existing logic changed.

### The cast

`Rat.normalize n d h` (`rat_prelude/ops.rs`) already existed — it takes an
`Int` numerator, a `Nat` denominator, and a proof `1 <= d`, and reduces to
lowest terms internally. That IS a `Rat.ofRat`-style cast; nothing needed
declaring in the kernel. `rat_lit(d, r: Rational) -> ExprId` is the one-line
builder this bridge lacked:

Detail moved to [`../notes/317-cas-fractional-cast.md`](docs/plan/notes/317-cas-fractional-cast.md).

**Your lane's block (`DONE for this slice`, ipc-provable, 2026-08-30).**
Task was slice 2 of `docs/plan/status/273-logic-excluded-middle.md`'s
decomposition: an inductive `Provable` relation for IPC natural deduction,
over the `Formula` AST slice 1 already landed in `ipc_heyting.rs`. Landed in
a new sibling file, `crates/axeyum-lean-kernel/src/ipc_provable.rs`.

**The relation's shape.** `FormulaList` (`nil | cons (head : Formula) (tail :
FormulaList)`) is the context type, built the same way `Formula` and `Str`
were — `Kernel::add_recursive_datatype_family` with `Formula` itself as the
(non-recursive) carrier sort. `Provable : FormulaList -> Formula -> Prop` is
a genuinely INDEXED `Prop`-valued inductive (`num_params = 0`, both arguments
are indices — unlike `Nat.le`'s fixed `n` or `Acc`'s fixed `(α, r)`, nothing
in `Provable` stays literally the same variable across a whole derivation,
since `weaken`/`or_elim`/`imp_intro` all change the context), built directly
via the general `Kernel::add_inductive` — the trusted gate that already
admits `Nat.le` (`nat_prelude/order.rs`) and `Acc` (`prelude.rs`), both
consulted as templates for "a hypothesis field that is a recursive
application of the family at a DIFFERENT index than the conclusion."

Eleven constructors, the standard IPC natural-deduction rules: `ax_head` +
`weaken` (together generating exactly "the goal occurs somewhere in the
context," since the kernel has no separate `Mem` relation either),
`and_intro`, `and_elim1`, `and_elim2`, `or_intro1`, `or_intro2`, `or_elim`,
`imp_intro`, `imp_elim`, `bot_elim`.

**What can be derived with it (kernel-checked, not asserted).** Two closed
theorems, each a genuine ND proof term through the trusted gate:
`ipc_provable_imp_self : Provable nil (imp p p)` (`imp_intro (ax_head)`) and
`ipc_provable_and_elim1_example : Provable nil (imp (and_ p q) p)`
(`imp_intro (and_elim1 (ax_head))`). Both admit on the first attempt and are
axiom-free (`Kernel::axiom_footprint` checked empty in-test).

Detail moved to [`../notes/318-ipc-provable.md`](docs/plan/notes/318-ipc-provable.md).

**Lane block (`DONE -- holdout-isolation green at held_out=96, two ADR-0542
amendments recorded, R10 binds the ledger to the v2 manifest, brief-step0
refuses a held-out target, holdout-amendment, 2026-08-30`).**

## Headline

`check-autogenesis-holdout-isolation.py` was `held_out=127|settled=10|FAIL` on
`main` and is now `held_out=96|settled=0|references=0|PASS`. No fact was
reopened; all ten are genuinely proved. The guard gap that produced the
incident is closed in three places, and the amendment is now machine-enforced
rather than recorded in a file nothing read.

Commits: `81c1aef5a`, `6f4b1e62b`, `137451362`, `1093e02f9`, `876ba7c47`,
plus the ADR commit below. **Not pushed.**

## 1. The dating -- the brief's reading held for 4 rows and not for 6

Declaration dates are the first commit introducing each
`<leaf>: kernel.name_str(nat, "<leaf>")` registration under `crates/`.

| fact | kernel theorem | declared | manifest | preregistered | blind then? |
| --- | --- | --- | --- | --- | --- |
| `F:ml430-nat-log-zero-left-9ec8541e` | `Nat.log_zero_left` | 2026-08-28 `3707c6040` | v1 | 2026-08-18 `2d65f19d8` | YES |
| `F:ml430-nat-log-zero-right-8ea186db` | `Nat.log_zero_right` | 2026-08-28 `3707c6040` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-of-lt-89eaf42e` | `Nat.log_of_lt` | 2026-08-28 `1dd090dff` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-le-self-da387172` | `Nat.log_le_self` | 2026-08-28 `722d9c204` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-left-1c61a5bf` | `Nat.clog_zero_left` | 2026-08-28 `2ccf6322c` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-right-d42d47b1` | `Nat.clog_zero_right` | 2026-08-28 `2ccf6322c` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-dvd-add-0c5bcc91` | `Nat.dvd_add` | 2026-08-13 `46b47f869` | v2-ext | 2026-08-29 `94b3e61ee` | **NO** |
| `F:ml430-nat-dvd-mul-right-a87a83c4` | `Nat.dvd_mul` | 2026-08-13 `46b47f869` | v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-add-iff-right-bf79c0cd` | `Nat.dvd_add_iff_right` | 2026-08-14 `eccaf84ac` | v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-antisymm-507f9026` | `Nat.dvd_antisymm` | 2026-08-24 `7de26df70` | v2-ext | 2026-08-29 | **NO** |

**Did anything leak? Not because of the sweep, and the two families differ.**

Detail moved to [`../notes/319-holdout-amendment.md`](docs/plan/notes/319-holdout-amendment.md).

**Your lane's block (`DONE for this slice`, ipc-eval, 2026-08-30).**
Task was slice 3 of `docs/plan/status/273-logic-excluded-middle.md`'s
decomposition (handed off in `docs/plan/status/318-ipc-provable.md`): a
generic `eval : Formula -> (Nat -> Nat) -> Nat` over `ipc_heyting.rs`'s
`Formula` AST, built as a genuine `Formula.rec` recursor application rather
than the one-off direct-`Nat` computation `ipc_heyting.rs` uses for its
single closed `pem_instance` countermodel check. Landed in a new sibling
file, `crates/axeyum-lean-kernel/src/ipc_eval.rs`. Depends only on slice 1
(`ipc_heyting.rs`); nothing from slice 2 (`ipc_provable.rs`, the `Provable`
relation) was needed, confirming the prior handoff's claim.

**The recursor application.** `Formula.rec.{1} motive m_var m_bot m_and_
m_or_ m_imp`, with motive `fun (_ : Formula) => (Nat -> Nat) -> Nat`
(non-dependent — constant in the `Formula` argument). One minor premise per
constructor, in declaration order:

- `m_var : Nat -> (Nat -> Nat) -> Nat := fun i v => v i`.
- `m_bot : (Nat -> Nat) -> Nat := fun v => 0`.
- `m_and_`/`m_or_`/`m_imp` : `Formula -> Formula -> motive_cod -> motive_cod
  -> motive_cod := fun a b ih_a ih_b v => op (ih_a v) (ih_b v)`, with `op`
  one of `meet3`/`join3`/`himp3` (already declared in `ipc_heyting.rs`).

`eval := fun (f : Formula) => Formula.rec.{1} motive … f`, a plain
`Definition`, admitted through the trusted `Kernel::add_declaration` gate.

Detail moved to [`../notes/319-ipc-eval.md`](docs/plan/notes/319-ipc-eval.md).

**DONE for this dispatch (`totient-mul`, 2026-08-30).** Landed two small,
fully-verified building blocks from `docs/plan/status/301-totient-
multiplicative.md`'s plan. Did NOT attempt `Nat.totient_mul_of_coprime`
itself, and did NOT attempt the CRT-bijection route `316-queue-sweep.md`
identified as the correct fix for `301`'s false `count_range_row_major`
claim — that remains the real remaining work, sized by `316` as several
more dispatches, and nothing in this session's budget changes that sizing.

## What already existed (did not need to build)

Before writing any code, ran `shape_search --include-constructed
--name-like coprime` (fresh build, `declarations=2301`) and `--name-like
gcd_mod`/`gcd_succ`. Confirmed landed by prior lanes and reused directly:

Detail moved to [`../notes/320-totient-bijection.md`](docs/plan/notes/320-totient-bijection.md).

## Status

LANDED. The frontier gate now fails at a floor instead of at zero, and there is
a repeatable, gated answer to "can the queue be refilled".

**The gate is RED on this branch, deliberately, at 3 dispatchable against a
floor of 10.** That is the true state of the queue, not a regression. It goes
green when someone authors a draw — which is now two names off a printed list
rather than a hand derivation.

## What was wrong, mechanically

Three candidate causes were on the table. Measured, not assumed:

1. **"The nursery is finite and mostly held-out, so it cannot be refilled."**
   Half right. 45% of every draw goes to held-out (the partition cycle restarts
   at index 0 per draw, so held-out takes `ceil(n/3)`, not a third — the
   committed manifest is 9/6/5 over 20 families). But the pool is not exhausted:
   **2,295 unused propositions survive every screen, across 94 modules, giving
   19 ready families.** A draw of all 19 would add 120 dispatchable rows.
   The queue can be refilled without going near a held-out row.

2. **"The extension pipeline has headroom but nothing runs it on a schedule."**
   This is the real cause, and it is worse than "nothing schedules it":
   **a refill is not a runnable operation at all.** `gen-autogenesis-nursery-
   refill.py` emits `PER_FAMILY * len(FAMILY_MODULES)` rows from two
   module-level dicts. Re-running it unchanged is a byte-level no-op that prints
   `AUTOGENESIS_NURSERY_REFILL_OK` and adds nothing. A draw is a SOURCE EDIT:
   add a family to `FAMILY_MODULES`, add its routes to `FAMILY_ROUTES`, re-run.
   Draws 2, 3 and 4 were all hand-authored on 2026-08-29 and nothing has run
   since.

   The drain rate makes that fatal: draw 4 put 110 non-held-out rows into the
   population and **107 were settled within a day**. The flywheel consumes
   population far faster than a human authors draws, and nothing computed
   whether a draw was even possible.

3. **"The statable screen may be too narrow a word list."** It is not a word
   list. `admissible = env | bridge`, where `env` is 2,207 declarations read
   from `kernel.environment()` and `bridge` is 70 constants DERIVED from settled
   mirrors. Every rejection names a constant this kernel does not declare. Do
   not loosen it — see ADR-0617 for what measuring it did turn up.

## What landed

Detail moved to [`../notes/321-queue-refill.md`](docs/plan/notes/321-queue-refill.md).

**Your lane's block (`DONE (kernel-reconstructed 10 -> 11; the "cast only"
sizing in docs/plan/status/317-cas-fractional-cast.md was WRONG for this
target -- see below; next cheapest cas-internal targets are
centroid-divides-medians / parallelogram-diagonals-bisect, cast+prove_mul,
both landed but not yet combined)`, cas-partial-fractions, 2026-08-30).**

## Step 0: verified the handoff rather than trusting it

`docs/plan/status/317-cas-fractional-cast.md` named
`F:cas-partial-fractions-mixed-general-case` "the cast only -- next lane's
cheapest target", in the same table as three `GeometryCertificate` facts
(`centroid-divides-medians`, `parallelogram-diagonals-bisect`, `euler-line`).

**That characterisation does not survive reading the fact.** Read directly:
`axeyum_cas::partial_fractions::PartialFractionCertificate` is a completely
different CAS module from `axeyum_cas::geometry_certify::GeometryCertificate`
-- no `cofactors`/`generators`/`conclusions` shape, no existing translator, and
(per the fact's own `notes` field, written 2026-08-27) "no kernel-side
partial-fraction route exists at all in this kernel." The "cast only" sizing
appears to have been carried over from the geometry facts in the same table
without checking that this one belongs to an unrelated module.

What was ACTUALLY needed, beyond the landed fractional cast:

1. A brand-new translator (`dense_to_rat_poly`) for this certificate's
   `Vec<Rational>`-dense, single-variable representation -- no
   `GeometryCertificate`-shaped translator applies to it.
2. A `Rational`-coefficient generalisation of
   `cas_geometry_mul_bridge_tests`'s `i128`-only polynomial x polynomial
   machinery (`prove_head_product`/`prove_term_mul`/`prove_poly_mul`/
   `prove_poly_combination`), because the quadratic factor's numerator
   (`Cx+D`) is genuinely non-constant -- the constant-cofactor-only
   `prove_scale_rat`/`prove_merge_rat`/`prove_const_combination_rat` the
   fractional-cast lane built cannot express that multiplication.

Detail moved to [`../notes/322-cas-partial-fractions.md`](docs/plan/notes/322-cas-partial-fractions.md).

**Lane block (`DONE — 127 violations to 3, graduation audited against the
pinned commit, 49 mutants each killed by exactly one test; the census has NO
SUBJECT and the gate stays red for that reason, mobility-census,
2026-08-30`).**

Commits: `8e4f0c5d9`, `fda827c93`, `a3d790b7a`, `e61fcd288`. **Not pushed.**
ADR: [ADR-0618](docs/research/09-decisions/adr-0618-graduation-is-lifecycle-a-census-dies-when-its-subject-closes.md).

## Headline

`python3 scripts/check-mobility-census.py` went from **127 violations to 3**,
and the three are distinct, actionable, and correct. The gate is **still red**,
and it should be: an entire documented capability measurement is currently void.

126 of the 127 were one sentence — `F:<id> is proved in the ledger; the census
is over OPEN facts`. That is the flywheel working. The census wrote 152 fact
rows; 126 of those facts have since been proved.

**Underneath that noise:**

| recomputed from the ledger / nursery / export index | |
|---|---:|
| census rows | 152 |
| … still open | 26 |
| … graduated (open at census time, settled now) | 126 |
| rows the census could EVALUATE | 3 |
| … of those, still open | **0** |
| zero-match clusters (the capability backlog) | 1 |
| … naming at least one still-open fact | **0** |
| entries in `agent-frozen-export-index-v1.json` | 4 |
| … whose fact is still open | **0** |

A frozen statement export is the **only** route to an evaluable goal — a
deliberate choice, argued in `docs/python-2026-08/07-mobility-census.md`: there
is no fallback that parses `formal.statement`, because that would make every
verdict rest on a goal nobody pinned. With zero open facts carrying one, the
census has no subject. **Regeneration cannot fix this**: `just
mobility-census-regen` would produce `evaluable = 0`, which the checker's rule 7
already refuses.

## Answers to the four questions in the brief

**1. What is the census FOR?** Well documented, not inferred.
`docs/python-2026-08/07-mobility-census.md` (slice A7) states it: take the model
out of the loop and ask a purely structural question — for each tactic and each
open fact, does the tactic's precondition hold at that fact's imported goal? It
exists because an earlier slice produced a false-negative rate nobody could
interpret. Its outputs are the tactic reach numbers, the zero-match clusters
(read as the capability backlog), and the headline evaluable/open ratio.

**2. Was the premise "no path to refresh it" right?** No — `just
mobility-census-regen` already existed and is documented in the justfile. The
real problem is worse than a missing refresh path: refreshing does not help.

Detail moved to [`../notes/323-mobility-census.md`](docs/plan/notes/323-mobility-census.md).

**Your lane's block (`DONE`, ipc-soundness, 2026-08-30).** Slice 4 of the
decomposition in `docs/plan/status/273-logic-excluded-middle.md`: soundness of
the `Provable` natural-deduction relation over the 3-element Heyting chain, and
the contraposition that closes the fact. All eleven cases check. **The fact is
closed** — `epistemic_status` open → proved, `proof_route` kernel-lean,
`axiom_footprint` `[]`, open since 2026-08-14.

Landed in `crates/axeyum-lean-kernel/src/ipc_soundness.rs` (+ `tests.rs`), with
a new checker example `crates/axeyum-lean-kernel/examples/ipc_soundness_inventory.rs`.

## The one finding that reshaped the slice

**The brief's soundness statement — `Provable ctx phi -> sat ctx v ->
eval phi v = top` — is not a statement an induction on the derivation can
carry, and `imp_intro` is the obstruction.** Its induction hypothesis is about
the *extended* context, so it says only *if `eval phi v = 2` then
`eval psi v = 2`*. The goal is `himp3 (eval phi v) (eval psi v) = 2`, i.e.
`eval phi v <= eval psi v`, and nothing in that hypothesis constrains the case
where `eval phi v` is the chain's **middle** element. The hypothesis is silent
exactly where the goal needs information — which is the whole reason the chain
has three elements rather than two.

The statement that does carry it is the standard algebraic one, over the meet
of the context:

    ipc_ctx_meet nil        v = 2
    ipc_ctx_meet (cons a l) v = meet3 (ipc_eval a v) (ipc_ctx_meet l v)

    ipc_soundness : forall ctx phi, Provable ctx phi
                  -> forall v, Le (ipc_ctx_meet ctx v) (ipc_eval phi v)

Read semantically: *the value of the context is below the value of anything
derivable from it*. `imp_intro` goes through by residuation, `or_elim` by the
chain's linearity.

**Nothing is lost.** `ipc_sat` is built as the brief asked (via
`FormulaList.rec`, `True` at `nil`, `And (Eq (eval a v) 2) …` at `cons`) and
bridged onto the meet — `ipc_sat_le_ctx_meet : ipc_sat l v -> Le 2
(ipc_ctx_meet l v)` — giving the sat-shaped corollary `ipc_soundness_sat`.

Detail moved to [`../notes/324-ipc-soundness.md`](docs/plan/notes/324-ipc-soundness.md).

## Status

LANDED. Draw 5: 60 rows across 6 families. Dispatchable **23 → 63**
against a floor of 10.

## The brief's premise was stale, and the correction matters

The task said the frontier gate was RED at 3 dispatchable. Measured on
arrival after merging local main, it was **green at 23**, exit 0,
`queue_below_floor: false`. The `321-queue-refill` handoff was written
before the ADR-0542 amendment lane landed (`6f4b1e62b`, `137451362`),
which moved `natural-logarithm` and `natural-divisibility` out of
held-out and returned their still-open siblings to the dispatchable set.

So this draw was not an emergency repair. It was still the right work:
draw 4 put rows into the population and **107 were settled within a
day**, so 23 is well under a day of headroom.

## What was drawn, and why six and not nineteen

Six is not a budget choice. The partition cycle assigns `ceil(n/3)` to
held-out, so **n=6 is the largest draw that opens only two held-out
slots**, and two is what R5 demands. n=7 opens a third, and there is not
enough held-out-safe supply for a third.

| primary module | family | partition |
| --- | --- | --- |
| `Init.Data.Int.Cooper` | integer-multiplicative-structure | held-out |
| `Init.Data.Int.Gcd` | integer-gcd-algorithm | development |
| `Init.Data.Nat.Gcd` | natural-gcd-algorithm | train |
| `Mathlib.Data.Int.LeastGreatest` | descent-and-well-ordering | held-out |
| `Mathlib.Data.Int.ModEq` | integer-congruence-lemmas | development |
| `Mathlib.Data.Nat.ModEq` | natural-congruence-lemmas | train |

## The partition assignment rule applied

Unchanged and mechanical: families sorted by the lexicographic path of
their **primary Mathlib module**, then cycled held-out / development /
train. `_with_cycle` freezes every earlier draw's family and runs the
cycle only over the new ones, so no existing family moved — asserted,
not assumed (`frozen unchanged: True`).

What a lane chooses is the family SET and each tuple's first element.
Both were chosen so the two held-out-**safe** families land at cycle
positions 0 and 3. Verified by running `assign_partitions()` before
generating anything.

On top of the mechanical rule, the discipline that decides which family
may be blind:

> A new family may go to held-out only if its mathematics is **not
> already published** by an existing development or train family. Beside
> another held-out family is fine (blind beside blind); beside a
> published one is the natural-division violation of ADR-0615.

Both held-out families were checked per module and are **R9-clean by
measurement**: 0 of the 10 selected rows in either has a declaration of
the same Mathlib name in the kernel environment.

Detail moved to [`../notes/325-nursery-draw.md`](docs/plan/notes/325-nursery-draw.md).

**Done (`golden-lean-check`, 2026-08-30).** Of the five golden-pin suites
(`diophantine_lean_reconstruct`, `quant_affine_growth_lean`,
`quant_counterexample_cover`, `quant_eq_partition_lean`, `quant_residue_lean`),
only diophantine's had a real-Lean check before this session; the other four
only asserted the rendered bytes matched a blessed `(length, fnv1a64)` hash — a
byte pin says nothing about whether Lean still accepts the module. Added a
`*_module_checks_in_real_lean` test to each of the four, following
diophantine's existing pattern (`lean_probe::lean_bin_or_skip` /
`report_checked`) exactly.

Verified in the foreground, one suite at a time, against the pinned Lean
4.30.0 (`AXEYUM_LEAN_BIN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`,
`AXEYUM_REQUIRE_LEAN=1`):

- `quant_affine_growth_lean`: 5 tests, 1 real-Lean check, 49.9 s wall (cold
  build; ~5.1 s of that is the suite itself).
- `quant_counterexample_cover`: 8 passed / 1 ignored, 1 real-Lean check,
  30.2 s wall (24.8 s suite; this suite's public-corpus reconstruction test
  is separately `#[ignore]`d, unrelated to this change).
- `quant_eq_partition_lean`: 7 tests, 1 real-Lean check, 6.1 s wall.
- `quant_residue_lean`: 4 tests, 1 real-Lean check, 5.7 s wall.
- `diophantine_lean_reconstruct` (unmodified, re-run as a control): 5 tests,
  1 real-Lean check, 6.4 s wall.

Total: **5 `[lean ok]` lines**, one per suite, all passing, none of them
`AXEYUM-LEAN-SKIPPED`. None of the added modules is disproportionately slow —
the four new checks each cost roughly the same single Lean invocation the
existing diophantine check already pays (order of 1-5 s of the suite's own
wall time; the affine-growth suite's larger wall time is a cold `cargo`
rebuild, not the Lean check itself).

Detail moved to [`../notes/326-golden-lean-check.md`](docs/plan/notes/326-golden-lean-check.md).

**Your lane's block (`DONE (kernel-reconstructed 11 -> 13; verified rather
than trusted the "already generic enough" claim -- it held for the
proof-emitting layer, but neither certificate's two-conclusions shape was
in the handoff's sizing; next cheapest cas-internal targets are
thales-right-angle-in-semicircle and varignon-midpoint-parallelogram, both
VACUOUS or near-vacuous identities cheaper than anything landed this
session)`, cas-geometry-pair, 2026-08-30).**

## Step 0: verified the "already generic enough" claim rather than trusting it

`docs/plan/status/322-cas-partial-fractions.md` named `centroid-divides-medians`
and `parallelogram-diagonals-bisect` as the next cheapest `cas-internal`
targets, and said the partial-fractions lane's new
`prove_poly_combination_rat` (and its three layers) were "already generic
enough to cover them ... they just need a `GeometryCertificate`-shaped parts
list instead of its `(numerator, cofactor)` one."

**The claim held at the proof-emitting layer, with zero new proof code.**
`prove_poly_combination_rat` was widened from module-private to
`pub(super)` in `cas_partial_fractions_bridge_tests.rs` (one-line change) and
called directly with `(cofactor, generator)` `RatPoly` pairs read from each
certificate. Nothing about `prove_head_product_rat`/`prove_term_mul_rat`/
`prove_poly_mul_rat`/`prove_poly_combination_rat` needed touching.

**What the handoff did NOT mention: both certificates have TWO conclusions
each** (centroid: `3P.x`/`3P.y`; parallelogram: midpoint-x/midpoint-y
agreement), and no existing module reconstructs more than one conclusion per
certificate. This needed two separate kernel theorems per certificate — an
ordinary application of the existing machinery, not new proof-emitting code,
but real additional test-writing and kernel-checking work the sizing table
did not surface.

Detail moved to [`../notes/327-cas-geometry-pair.md`](docs/plan/notes/327-cas-geometry-pair.md).

**Done (`archive-provenance`, 2026-08-30).** `98d17aeef` archived 346 `check-*` scripts on "no live
caller in `check.sh` or the justfile". That criterion could not see artifact
citations, which are callers of a different kind.

Measured before the fix: 212 distinct script names cited by files under
`artifacts/`; 87 resolved into `scripts/`, **125 only into `scripts/archive/`**,
0 nowhere. 111 of those pairs spell an explicit `scripts/check-X.py`, so 111
committed artifacts carried a false path.

The two surfaced failures were not check failures. Every archived script uses
`ROOT = ...resolve().parents[1]`, which is `scripts/` itself one level deeper —
**345 of 345** archived files (control: 256 live ones, where it is correct). The
sweep made every archived script unable to run.

**Restored 129, kept 217 archived.** 125 cited directly, 4 by transitive closure
through sibling invocation — a second caller class the census also missed
(capsule checkers invoke result checkers by path; control: 175 references that
resolve). Restoring makes `parents[1]` right *and* the artifacts' spelling true,
so no script and no artifact needed editing.

Running all 129: **103 pass, 26 fail**. The split is the finding — capsule
16/16, result 31/33, plan 52/76. Result and capsule checkers re-verify frozen
artifacts and should pass forever; plan checkers assert live-tree preconditions
and go stale by design. So the gate asserts **resolvability, not exit 0** —
requiring exit 0 would red on 24 correctly-stale plans.

`scripts/check-artifact-gate-provenance.py` (ADR-0621), registered in both
aggregate gates, green at `artifact_citations=578|sibling_references=183|
live=601|archived=216`. Seven guards, each mutation-verified to kill exactly one
of 11 controls, no survivors.

Cleared: `check-autogenesis-modeq-family.py` and
`check-autogenesis-bounded-induction-family.py` (exit 1 → `_OK`), plus three
sealed-capsule receipts nobody could re-check (`nat-fib-dvd`, `nat-fib-gcd`,
`int-fib-natcast`).

**Next:** a future archiving sweep needs "no live caller AND no artifact
citation"; the gate names the artifact and script when it fires. Open question
in ADR-0621: whether the 217 still-archived scripts should get a
location-independent root. Nothing claims they run today, and restoring one
self-heals the idiom.

**Your lane's block (`DONE for this pass`, nat-modeq-mirrors, 2026-08-30).**
6 of the 10 dispatchable `ml430-nat-modeq` mirrors closed; 4 left open with a
precise blocker each (below). `nat_prelude/modular.rs` already carries a full
`Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` congruence family (refl, symm,
trans, add_left/right/both, mul_left/right/both, and `euler.rs`'s coprime
multiplicative cancel `mod_eq_cancel`) — none of it was wired to any fact
before this lane, and `F:ml430-nat-modeq-add-1561afa8` turned out to already be
exactly `Nat.mod_eq_add`, no new proof needed.

Closed (new file `crates/axeyum-lean-kernel/src/nat_prelude/modeq_add_cancel.rs`,
wired in right after `declare_gcd_comm`, since `mod_eq_cancel_left` needs
`gcd_comm`):

- `F:ml430-nat-modeq-add-1561afa8` — `Nat.mod_eq_add` (pre-existing, flip only)
- `F:ml430-nat-modeq-add-iff-left-b719aac5` — `Nat.mod_eq_add_iff_left`
- `F:ml430-nat-modeq-add-iff-right-84daa45f` — `Nat.mod_eq_add_iff_right`
- `F:ml430-nat-modeq-add-left-cancel-fb96581c` — `Nat.mod_eq_add_left_cancel`
- `F:ml430-nat-modeq-add-right-cancel-f0ab48e4` — `Nat.mod_eq_add_right_cancel`
- `F:ml430-nat-modeq-cancel-left-of-coprime-f89af373` — `Nat.mod_eq_cancel_left`
  (same content as `mod_eq_cancel`, coprimality's `gcd` argument order flipped
  via `gcd_comm` to match this mirror's `m.gcd c = 1` vs. `mod_eq_cancel`'s
  `gcd c n = 1`)

All five new theorems compose only already-checked lemmas
(`mod_eq_add_left`/`_right`/`_symm`/`_trans`/`mod_eq_add`/`gcd_comm`/
`mod_eq_cancel`) plus two `euler.rs` helpers exported `pub(super)` for this
purpose: `cancel_common_right_addend` (`modEq n (a+k) (b+k) → modEq n a b`,
needs no side condition — additive cancellation is easier than the
multiplicative case `mod_eq_cancel` needs Bezout for) and `rewrite_mod_eq`
(transport a `modEq` across an `Eq` on each endpoint). No new
existential-elimination term was written in this pass.

Detail moved to [`../notes/329-nat-modeq-mirrors.md`](docs/plan/notes/329-nat-modeq-mirrors.md).

**Your lane's block (`DONE (9 of 14 dispatchable log/clog mirrors closed;
5 remain open with a scoped handoff below -- log_le_clog is the cheapest
next target, its whole proof sketch is written out; the two AntitoneOn
facts are NOT blocked by a missing Set type the way this task's brief
assumed, they are blocked by a genuinely new monotonicity-in-the-base
lemma nobody has built)`, nat-log-mirrors, 2026-08-30).**

## Closed: 9 of 14

Four already existed as admitted kernel theorems before this lane started
(built by the `log.rs`/`clog.rs` lane on 2026-08-28, never flipped as `ml430`
mirrors): `Nat.log_one_left`, `Nat.log_one_right`, `Nat.clog_one_left`,
`Nat.clog_one_right`. No new proof work for these four — verified the
rendered kernel type against `formal.statement` character-by-character via
`nat_theorem_inventory --release` and flipped status.

Five are new kernel constructions, all in the new
`crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`:

Detail moved to [`../notes/330-nat-log-mirrors.md`](docs/plan/notes/330-nat-log-mirrors.md).

**Eleven mirrors closed (`WIP` -> mostly done, nat-gcd-dvd-mirrors,
2026-08-30).** Of the nineteen dispatchable in this area, closed:

- **Two pure flips, no new proof.** `F:ml430-nat-dvd-gcd-e5184fc5` and
  `F:ml430-nat-dvd-gcd-iff-b8485987` are `Nat.dvd_gcd`/`Nat.dvd_gcd_iff`,
  which predate this session (`declare_gcd_semantics`, `nat_prelude/gcd.rs`).
  The rendered type matches `formal.statement` exactly; closed by evidence
  only.
- **Nine new proofs**, all in the new file
  `crates/axeyum-lean-kernel/src/nat_prelude/gcd_dvd_mirrors.rs`, wired in
  with one `declare_gcd_dvd_mirrors` call:
  `Nat.dvd_mul_left`, `Nat.dvd_mul_left_of_dvd` (not in the original
  nineteen-item list but dispatchable in the same shape-search sweep and
  equally cheap — `dvd_mul_right_of_dvd` + `mul_comm`),
  `Nat.eq_zero_of_gcd_eq_zero_{left,right}`, `Nat.dvd_mod_iff_gen`,
  `Nat.div_mul_cancel`, `Nat.dvd_iff_mod_eq_zero`, and
  `Nat.div_gcd_pos_of_pos_{left,right}`.

All nine new declarations are axiom-free (`nat: axiom=0 opaque=0
quotient=0`), registered in `theorem_names`/`the_build_is_deterministic`'s
pin (669 -> 676 after the first seven, -> 678 (`93 + 585`) after the two
`div_gcd_pos_of_pos_*` theorems), and covered by the environment-derived
`every_nat_declaration_is_checked_and_axiom_free` assertion. Full
`nat_prelude::` sweep: 181 passed, 0 failed.

Every fact's `checker_command` was run directly (not just written): the
exact-name `grep -Ec '^Nat\.<name>[[:space:]]'` was checked to discriminate
against the substring-overlapping sibling in each case that has one
(`dvd_gcd` vs `dvd_gcd_iff`, `div_mul_cancel` vs `div_mul_cancel_of_dvd`,
`div_gcd_pos_of_pos_left` vs `_right`), and `nat_axiom_inventory
--require-axiom-free nat` was run and confirmed `nat: axiom=0 opaque=0
quotient=0` after every batch.

Partition check before touching any fact: all eleven are `train`/
`development` in `artifacts/autogenesis/nursery-v2-extension.json` — none
held-out.

Detail moved to [`../notes/331-nat-gcd-dvd-mirrors.md`](docs/plan/notes/331-nat-gcd-dvd-mirrors.md).

**Your lane's block (`DONE (kernel-reconstructed 13 -> 14; thales
kernel-reconstructed with a full disclosure that its cofactor identity is
refl-shaped, not a genuine combination; varignon deliberately NOT
reconstructed -- its certificate has zero coordinates, zero generators, and
an already-empty conclusion polynomial, so reconstructing it would produce
Rat.zero = Rat.zero with no geometric content at all; next cheapest
cas-internal target is pappus-hexagon)`, cas-thales-varignon, 2026-08-30).**

## Step 0: verified the sizing rather than trusting it

`docs/plan/status/327-cas-geometry-pair.md` named both targets "reachable
with the ORIGINAL constant-cofactor-only machinery
(`cas_geometry_bridge_tests.rs`'s `prove_const_combination`)... possibly the
cheapest reconstruction in the whole geometry family." That much is TRUE for
thales and held with zero new proof-emitting code. But the same handoff, and
— it turns out — the orthocentre sibling fact's own `notes` field (written
2026-08-29, before this lane started) already contained the finding that
matters more than the sizing:

> "thales' single cofactor is the constant 1 against a conclusion
> byte-identical to its generator, so the kernel obligation there is refl."

This lane verified that claim directly against the CAS's own certificate
(`artifacts/geometry-certificates/thales-right-angle-in-semicircle.json`):
`cert.generators[0]` and `cert.conclusions[0].poly` are BYTE-IDENTICAL as
`IntPoly` (same 8 terms, same coefficients), and the cofactor is the constant
`1`. Since `poly_expr` is a deterministic function of its `IntPoly` input,
the kernel statement this bridge builds is literally `poly_expr(X) =
Rat.ofInt 1 * poly_expr(X)` for one specific `X` — a `mul_one`-shaped ring
fact true of ANY polynomial whatsoever, not one that discriminates Thales'
theorem from any other. The genuinely geometric coincidence — that "C lies
on the circle with diameter AB" and "CA ⟂ CB" expand to the IDENTICAL
polynomial — is checked only by a plain Rust `assert_eq!` in the translator
test, never by `Kernel::add_declaration`.

Detail moved to [`../notes/332-cas-thales-varignon.md`](docs/plan/notes/332-cas-thales-varignon.md).

**Status: LANDED.** `scripts/check-cas-substance.py` is green on the committed
ledger and registered in both `scripts/check.sh` and the `justfile`
(`check-aggregate-scope.sh` green, 66 recorded differences, no new one-sided
step). Decision recorded in
[ADR-0622](docs/research/09-decisions/adr-0622-a-reconstruction-must-say-what-it-establishes.md).

## The deficiency

`scripts/validate-facts.py`'s `classify_cas_certificate_checker` returns
`kernel-reconstructed` when some executed `cargo test` / `cargo run` segment
merely NAMES the `axeyum-lean-kernel` package. It never inspects what the kernel
was asked to check. So the headline

    cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28

moved identically for `poly_expr(X) = Rat.ofInt 1 * poly_expr(X)` — true of
every polynomial — and for a six-variable identity with real cancellation.

## The measurement, all 14

Derived by `scripts/cas_substance.py` from the certificate the CAS emitted,
where one exists; declared by the fact where none does. `in`/`out` are monomials
entering the combination and remaining in the conclusion, per conclusion.

| fact | shape | provenance | active gens | in → out |
| --- | --- | --- | --- | --- |
| `F:geometry-centroid-divides-medians-kernel-checked` | `combination` | derived | 3 | 88 → 4 (×2) |
| `F:geometry-medians-cofactor-identity-kernel-checked` | `combination` | derived | 2 | 20 → 10 |
| `F:geometry-orthocentre-cofactor-identity-kernel-checked` | `combination` | derived | 2 | 16 → 8 |
| `F:geometry-parallelogram-diagonals-bisect-kernel-checked` | `combination` | derived | 3 | 60 → 4 (×2) |
| `F:geometry-rhombus-cofactor-identity-kernel-checked` | `combination` | derived | 4 | 264 → 8 |
| **`F:geometry-thales-cofactor-identity-kernel-checked`** | **`refl`** | derived | 1 | **8 → 8, zero cancellation** |
| `F:cas-difference-of-squares-free-x-kernel-checked` | `identity` | declared | — | free `x` |
| `F:cas-partial-fractions-mixed-general-case-kernel-checked` | `identity` | declared | — | `forall x` |
| `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-extremum-deriv-sign-bracket-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve` | `evaluation` | declared | — | concrete |
| `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-mvt-secant-endpoints-kernel-checked` | `evaluation` | declared | — | concrete |
| `F:cas-taylor-remainder-lhs-kernel-checked` | `evaluation` | declared | — | concrete |

Detail moved to [`../notes/333-cas-substance-gate.md`](docs/plan/notes/333-cas-substance-gate.md).

**The aggregate gate is time-bounded, and the bound is proved to fire**
(`landed`, gate-termination, 2026-08-30). `scripts/check.sh` had **zero**
timeout-guarded steps of 401, so one hung step hung the gate forever — a live
run was reaped after **nine hours**, 0% CPU at every level, reparented to init,
log stopped mid `=== facts-replay ===`. Every step now carries a generous
per-step cap and a third outcome, `TIMED OUT` = UNCHECKED, which is counted and
named separately from a failure and can never read as a pass (ADR-0623).

**The second finding was worse than the first.** `scripts/check-fast.sh` had a
per-step cap from the day it was written and it did not bind: `timeout N` sends
SIGTERM and then waits **forever** while still exiting 124, so a caller testing
for 124 sees a correct-looking verdict after an arbitrarily long wait. A run of
it was found stuck 23 minutes on a step with a 3-second budget. A cap nobody has
watched bite is a cap you do not have — which is why the deliverable is a probe,
`scripts/check-gate-step-timeout.sh`, registered in both aggregate gates. It is
the time analogue of `cargo-serialized.sh --self-check`.

**`--kill-after` is necessary and not sufficient**, and the probe is what found
that. `timeout` signals the child it monitors, not the tree beneath it, and
`trap '' TERM` sets SIG_IGN which is inherited across exec. Measured at a 2s cap
with an uncapped positive control, in two fixture shapes:

| | sleeper last | sleeper backgrounded |
| --- | --- | --- |
| uncapped (control) | 1 | 1 |
| `timeout -k` | 1 | 1 |
| `timeout -k`, group kill omitted | 1 | 1 |
| `timeout -k` + `kill -KILL -$pgid` | **0** | **0** |

That surviving grandchild IS the nine-hour bug: an orphaned `cargo` holds the
build-directory lock, whose wait is unbounded, so every later cargo step blocks
on a process nothing will reap. 4,064 of the ledger's 4,122 `checker_command`s
invoke cargo.

Detail moved to [`../notes/334-gate-termination.md`](docs/plan/notes/334-gate-termination.md).

**Fourteen of twenty dispatchable mirrors closed (`WIP` -> mostly done,
int-dvd-mirrors, 2026-08-30).**

- **Two pure flips, no new proof.** `F:ml430-int-dvd-coe-gcd-6bda035e` is
  `Int.dvd_gcd` (our internal name), which is Mathlib's `Int.dvd_coe_gcd`
  (an **Int**-typed divisor, cast around `a.gcd b`) — predates this lane
  (`gcd.rs`'s `declare_dvd_gcd`). `F:ml430-int-modeq-add-right-fa8f7abe` is
  `Int.modEq_add_right` (rendered name is camelCase, not the Rust field's
  snake_case `mod_eq_add_right`) — already unconditional in the modulus,
  predates this lane. Both closed by evidence only, no code.
- **Twelve new proofs**, all in the new file
  `crates/axeyum-lean-kernel/src/int_prelude/dvd_gcd_mirrors.rs`, wired in
  with one `dvd_gcd_mirrors::declare_all` call at the very end of
  `build_int_prelude`'s sequence (after every dependency):
  `Int.dvd_gcd_nat`/`Int.dvd_gcd_nat_iff` (Mathlib's actual `Int.dvd_gcd`/
  `.dvd_gcd_iff` — Nat-typed divisor, distinct from the coe form above),
  `Int.dvd_coe_gcd_iff`, both `Int.ediv_gcd_ne_zero_*` facts,
  `Int.mod_eq_add`, `Int.mod_eq_add_right_cancel` (single-`c` form,
  Mathlib's `.add_right_cancel'`), `Int.mod_eq_add_left_cancel_general` /
  `Int.mod_eq_add_right_cancel_general` (4-variable forms — **not** the
  same propositions as the existing single-`c` `mod_eq_add_left_cancel`,
  despite the name overlap), `Int.mod_eq_dvd`, `Int.mod_eq_emod_eq`, and
  `Int.mod_eq_mul_general` (Mathlib's `Int.ModEq.mul`, genuinely
  UNCONDITIONAL — the existing `p.mod_eq_mul` needs `0 < n`).

Detail moved to [`../notes/335-int-dvd-mirrors.md`](docs/plan/notes/335-int-dvd-mirrors.md).

**Done (`gcd-mul-right`, 2026-08-30).** `docs/plan/status/331-nat-gcd-dvd-mirrors.md`
left three `ml430` facts open, all blocked on one missing distributive lemma:
`Nat.gcd_mul_right : ∀ a b c, gcd (a*c) (b*c) = gcd a b * c`.

**Verified the lemma was genuinely absent, not a naming miss**, before writing
any induction: grepped `nat_prelude/gcd.rs` and `nat_prelude/lcm_gcd_lemmas.rs`
in full for any `gcd_mul_*` spelling (nothing), and `int_prelude/gcd.rs`'s own
module doc (around its `Int.gcd_div` construction) states explicitly that
neither `Nat.gcd_mul_left` nor `gcd_mul_right` exists in this development and
that building either needs a fresh strong-induction principle over `gcd`'s
well-founded recursion. (`Int.gcd_mul_right`, in that same file, is an
unrelated coprimality-descent proposition sharing the Mathlib name — checked
and ruled out as a transportable shortcut.)

**Built it**: `crates/axeyum-lean-kernel/src/nat_prelude/gcd_mul_right.rs`,
well-founded induction on the first argument mirroring `declare_gcd_bezout`'s
WF-fix scaffolding (`bezout.rs`) exactly — same relation (`lt_well_founded`),
same `family`/`step_motive`/`step` pattern. Two supporting pieces, both new:

- `mul_mod_mul_right_eq : mod(n*c, m*c) = (mod n m)*c` for positive `m` (built
  via `div_mod_reconstructed` + `div_mod_unique`, mirroring `mod_mul_eq`'s
  proof shape in `mod_mul_lemmas.rs`).
- `gcd_unfold_pos : gcd x y = gcd (mod y x) x` for arbitrary positive `x`,
  generalizing `gcd_succ` (which needs its first argument literally of shape
  `succ _`) the same way `div_mod_reconstructed` generalizes `div_mod_exec`.

Wired in as the LAST `declare_*` call in `build_nat_prelude`.

Detail moved to [`../notes/336-gcd-mul-right.md`](docs/plan/notes/336-gcd-mul-right.md).

**Your lane's block (`DONE (3 of 5 remaining log/clog mirrors closed --
log_le_clog, log_lt_self, log_antitone_left; 2 remain open with precise
obstacles below -- clog_antitone_left needs a genuinely new
ceiling-division-monotonicity lemma with a nontrivial numerator-form
bridging identity; log2_eq_log_two needs a new WellFounded.fix-based
Nat.log2 definition from scratch plus evaluation tests plus a mirror-flip
check)`, log-clog-finish, 2026-08-30).**

Picked up from `docs/plan/status/330-nat-log-mirrors.md`'s handoff (9 of 14
`nat-log`/`nat-clog` mirrors closed there). This lane closed 3 of the
remaining 5.

## Closed: 3 of 5

All in `crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`.

- **`Nat.log_le_clog : ∀ b n, Le (log b n) (clog b n)`.** New
  `Nat.log_aux_le_clog_aux : ∀ b f n, Le (logAux b f n) (clogAux b f n)` —
  the two aux FAMILIES compared at a SHARED fuel (both `log`/`clog` are
  diagonal at `f := n`, unlike `log_aux_mono`/`clog_aux_mono`, which compare
  one family against itself at two DIFFERENT fuels). Induction on `f` (`n`
  generalized inside the motive), splitting on three booleans: `2 ≤ b`
  (log's inner cut, clog's outer cut — the SAME test), `b ≤ n` (log's outer
  cut only), `2 ≤ n` (clog's inner cut, derived from the first two via
  `le_trans` rather than split independently). New small helper
  `n_le_add_sub_one : Le n (sub (add n base) 1)` for `Le 1 base`
  (`add_le_add_left` then `pred_le_pred`, using that `sub x 1` is
  definitionally `pred x`), giving `n/b ≤ (n+b-1)/b` via `div_le_div_right`;
  the hard leaf chains the induction hypothesis at `n/b` through
  `clog_aux_mono` via `le_trans`, then `le_succ_succ`.

Detail moved to [`../notes/337-log-clog-finish.md`](docs/plan/notes/337-log-clog-finish.md).

**Done (`int-gcd-mul-transport`, 2026-08-30).** `docs/plan/status/335-int-dvd-mirrors.md`
left three `ml430` facts open, all blocked on `Nat.gcd_mul_right`.
`docs/plan/status/336-gcd-mul-right.md` built that lemma and its three `Nat`
mirrors within the hour. This lane merged both and did the ℤ transport.

**All four targets closed, no re-derivation needed at the `Int` layer:**

- `F:ml430-int-dvd-gcd-mul-iff-dvd-mul-12f61b99`
- `F:ml430-int-dvd-mul-gcd-iff-dvd-mul-22d6488e`
- `F:ml430-int-dvd-gcd-mul-gcd-iff-dvd-mul-8ea752a5`
- `F:ml430-nat-dvd-add-iff-left-332cbe04`

**The ℤ→ℕ transport held, and the mechanism is worth recording.** `Int.gcd a b
:= Nat.gcd (natAbs a) (natAbs b)` (`gcd.rs`), and `Int.dvd` is equivalent to
`Nat.dvd` on magnitudes in both directions
(`nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd`, `gcd.rs`), and `natAbs` is
multiplicative (`nat_abs_mul`, `gcd.rs`). Composing these three turns any
`k ∣ x*y` statement (`k, x, y : ℤ`) into `natAbs k ∣ natAbs x * natAbs y`, and
specializing `x := ofNat (k.gcd n)` lands on exactly the `Nat`-level
`dvd_gcd_mul_iff_dvd_mul` at `(natAbs k, natAbs n, natAbs m)` — the kernel
resolves `natAbs (ofNat c) ≡ c` and `Int.gcd k n ≡ Nat.gcd (natAbs k) (natAbs
n)` on its own via `def_eq` at `add_declaration` time (both are bare
delta/iota reductions), so no explicit bridging LEMMA is needed for either —
only the genuinely non-defeq step, `natAbs`'s multiplicativity, needs a real
proof term in the chain.

New file `int_prelude/gcd_scaled_mirrors.rs`:
`idvd_mul_iff_nat_dvd_mul(k,x,y) : Iff (idvd k (x*y)) (Nat.dvd (natAbs k)
(natAbs x * natAbs y))` is the general bridge; `int_dvd_gcd_scaled_iff(k,b,c) :
Iff (idvd k ((ofNat (k.gcd b))*c)) (idvd k (b*c))` specializes it and chains
against the `Nat`-level fact — this is `Int.dvd_gcd_mul_iff_dvd_mul` directly
at `(b,c) := (n,m)`. `Int.dvd_mul_gcd_iff_dvd_mul` commutes both sides of the
shape applied at `(b,c) := (m,n)` into place with `Int.mul_comm`, mirroring
`nat_prelude/gcd_mul_right_mirrors.rs`'s `dvd_mul_gcd_iff_dvd_mul` one layer
up. `Int.dvd_gcd_mul_gcd_iff_dvd_mul` applies the shape at
`c := ofNat (k.gcd m)` and chains one more `Iff.trans` against
`dvd_mul_gcd_iff_dvd_mul` — so that one had to be declared first, same
dependency order as the `Nat` file.

Detail moved to [`../notes/338-int-gcd-mul-transport.md`](docs/plan/notes/338-int-gcd-mul-transport.md).

**Done (`modeq-div-gcd`, 2026-08-30).** All five facts closed:

- `F:ml430-nat-modeq-cancel-left-div-gcd-57ef8287`
- `F:ml430-nat-modeq-cancel-right-div-gcd-22a4f40d`
- `F:ml430-nat-modeq-cancel-left-div-gcd-cfca1225`
- `F:ml430-int-modeq-cancel-left-div-gcd-b2d407e8`
- `F:ml430-int-modeq-cancel-right-div-gcd-00cd73fa`

Two prior lanes (`nat-modeq-mirrors`, `docs/plan/status/329-nat-modeq-mirrors.md`;
`int-dvd-mirrors`, `docs/plan/status/335-int-dvd-mirrors.md`) had sized this
whole family as needing a new "divide-by-gcd factorization" slice, built
around `Nat.gcd_mul_right` (which landed for a sibling family within the
hour before this lane started). **`gcd_mul_right` turned out NOT to be what
unlocks this family, on either carrier.** What actually closes it:

Detail moved to [`../notes/339-modeq-div-gcd.md`](docs/plan/notes/339-modeq-div-gcd.md).

## Status

DONE. `check-dispatchable-frontier.py` is green; the statable vocabulary is now
derived rather than hand-maintained (ADR-0624).

## What the vocabulary decides

`artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` is the positive
screen for *statable in this kernel*:

    admissible = env      2,207 names read from kernel.environment()
               | bridge   70 constants of SETTLED ml430 mirrors, minus env

A candidate passes iff every Lean constant in its pinned `type_repr` is
admissible. It rejects 5,399 of the 9,729-record pinned pool, so it is not
vacuous.

**It has no per-row boolean `settled` flag**, despite the gate docstring's
wording. `settled` is a LIST of `{source_name, constants}` rows, and membership
is what promotes a row's constants into `bridge`.

## Nothing in the artifact was a free choice

S2 bounds `bridge` from below (every entry must be witnessed), S3 bounds it from
above (every settled row must be admissible) — together they pin it to ONE
value. S4 pins the row set to the ledger both ways. Verified on the committed
file: `bridge == witnessed − env` exactly, 70/70; and each row's `constants`
re-derive from the pinned inventory's `type_repr`, **162/162**.

The one field no gate touches is a row's `constants` — and that is the field
that matters. A hand-appended row with invented constants passes S2, S3 and S4
whenever another row redundantly witnesses them.

## The 9: all new rows, zero corrected flags

All nine are `proved`; nothing was listed-but-not-settled, so the drift was
entirely one-directional.

    Nat.clog_mono_right   Nat.clog_monotone   Nat.clog_one_left
    Nat.clog_one_right    Nat.clog_pos        Nat.log_mono_right
    Nat.log_monotone      Nat.log_one_left    Nat.log_one_right

**The repair did not widen the screen**, which is the measurement that matters:

    rows    162 -> 171    0 removed, 0 CHANGED, 9 added
    bridge   70 ->  70    0 added, 0 removed

`Nat.clog` / `Nat.log` are in the ENVIRONMENT, not the bridge — the pool grew
because the kernel DECLARED them, exactly ADR-0619's rule.

Confirmed downstream: `propose-nursery-refill.py`'s R2 fired on the changed
digest, and re-measuring changed **exactly one leaf** of the headroom snapshot
(`/input_digests/vocabulary`). All 5,399 / 2,235 / 15 counts identical.

## Holdout gate

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1107|settled=0|references=0|verdict=PASS

Identical to the pre-change baseline except `files_scanned` 1106 -> 1107 (the
new constants cache). No held-out row was touched; the artifact is keyed by
Mathlib `source_name` and never by `fact_id`.

## What was built so this does not recur

Detail moved to [`../notes/340-vocabulary-drift.md`](docs/plan/notes/340-vocabulary-drift.md).

**Status: done.** Per-step detail in
[`docs/plan/notes/341-gate-cleanup.md`](docs/plan/notes/341-gate-cleanup.md).

    before   declared=404|ok=248|failed=43|deferred=113
    after    declared=405|ok=273|failed=17|deferred=115

All 43 were re-run at merged HEAD first and all 43 still failed, so none was a
stale-list artifact. **26 no longer fail** — 24 fixed, plus 2 reclassified as
host-conditional and deferred. **17 left red with reasons.**

The one real defect: a spurious `depends_on` back-edge made the fact DAG cyclic
(`log_mono_right` <-> `log_monotone`), which exited `gen-autogenesis-baseline.py`
at 2 and froze every artifact downstream of it. The source settles the direction
and the `clog` pair is the positive control.

The largest group was drift, and its size is the finding: ten generated views
were describing a **698-fact** ledger against an actual **2,220**.
`facts_via_multi_target` did NOT rise with them — 30 before and after.

Three fixes were real defects rather than drift: a census that had crashed on
every run for six days, a check reading only the first occurrence of each claim
it gates, and two CI revisions pinned under keys naming no repository.

**Held-out is intact and was never touched.** Neither nursery manifest is
modified in any commit here:

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1106|settled=0|references=0|verdict=PASS

Deliberately still red: `autogenesis-nursery` (three `depends_on` components
span development/train — none reaches held-out; the fix is an ADR-0542
amendment, not gate work), `development-partition`, `mobility-census` (3 real
violations another lane kept red today), `local-ci-freshness` (needs a real CI
run), `plan-authority` (systemic, 1.98 MB of status files), `obstruction-graph`
(an unclassified decline shape it correctly refuses to drop), and six pinned
counts I could not verify as legitimate moves.

<!-- /plan-section -->

**Lane:** `bridge-elision` · **Date:** 2026-08-30 · **Status:** landed
**Decision:** [ADR-0631](docs/research/09-decisions/adr-0631-a-closure-licenses-a-constant-only-if-the-proof-mentions-it.md)

## The deficiency

The statable-vocabulary bridge promotes a Mathlib constant whenever a mirror
whose pinned statement mentions it closes. That inference fails when the mirror
was closed by **eliding** the constant. `F:ml430-nat-log-antitone-left` pins
`AntitoneOn (fun b => Nat.log b n) (Set.Ioi 1)` and promoted both constants
(bridge 70 → 72); our theorem is the pointwise
`Le x1 x2 → Lt 1 x1 → Lt 1 x2 → Le (log x2 x0) (log x1 x0)`, mentioning
neither and needing no `Set` type. Precision problem, not soundness — nothing
in the fact ledger is wrong and nothing was reopened.

## Blast radius, measured before building anything

Method: join each settled catalogued mirror to its fact's
`formal.kernel_statement` (the rendered kernel type, already in the ledger — no
cargo run needed), then ask per bridge constant whether any mirror that
promoted it mentions it. Reproduce: `python3
scripts/measure-bridge-elision-radius.py`.

    bridge 72 = elaboration 50, expressed 2, elided 8, unrendered 12
    open pooled propositions 28, statable 24
      admitted ONLY via an elided constant     2
        Nat.clog_antitone_left    via AntitoneOn, Set.Ioi
        Nat.coprime_of_lt_minFac  via Nat.Coprime, Ne
      admitted ONLY via an unrendered constant 3
        Nat.testBit_land / _ldiff / _lor        via Bool.and / Bool.not / Bool.or
      conservative statable                   19  (headline 24)
    positive control: statable under env alone 0

`F:ml430-nat-clog-antitone-left` is LIVE in the frontier's DISPATCHABLE set —
the direct sibling of the incident. `Nat.coprime_of_lt_minFac` is already
blocked by the divergence registry over `Nat.minFac`, so exactly one of the two
would actually have cost a lane. On the nursery-v2 extension the reach is
larger: **72 of 260** preregistered candidates are elision-backed.

The 8 elided constants, with the evidence behind each promotion:

    AntitoneOn    1 witness  (1 rendered)     Nat.Coprime  22 (10)
    Set.Ioi       1          (1)              Nat.ModEq    19 (1)
    Monotone      4          (2)              Nat.Prime    15 (2)
    Nat.cast      9          (1)              Ne           10 (1)

Detail moved to [`../notes/342-bridge-elision.md`](docs/plan/notes/342-bridge-elision.md).

**Done (`dvd-mul-split`, 2026-08-30).** `F:ml430-nat-dvd-mul-ebd102e2` closed.
`F:ml430-int-dvd-mul-3a7b94cd` stays open — precise blocker below, not a
re-derivation of the "no short route" verdict two prior lanes already gave it.

## `Nat.dvd_mul_split` — closed

Two prior lanes called `k ∣ m*n ↔ ∃ k1 k2, k1∣m ∧ k2∣n ∧ k1*k2=k` a
factorization-existence statement with no short route. Both sized it before
`Nat.gcd_mul_right` existed (landed the same day, lane `gcd-mul-right`) and
neither reports having tried the gcd construction. With `gcd_mul_right` in
hand it is not a factorization problem at all:

- **Forward.** `k1 := gcd(k,m)`, `k2 := k/gcd(k,m)`. `k1 ∣ m` is
  `gcd_dvd_right` directly. `k1*k2=k` comes from eliminating `gcd_dvd_left`'s
  witness. The one piece of real content, `k2 ∣ n`: `k ∣ k*n` (`dvd_mul`) and
  `k ∣ m*n` (hypothesis) combine via `dvd_gcd` into `k ∣ gcd(k*n,m*n)`;
  `gcd_mul_right` rewrites the gcd to `k1*n`, giving `k ∣ k1*n`; substituting
  `k = k1*k2` gives `k1*k2 ∣ k1*n`; cancelling the positive common factor
  `k1` (`one_le_of_dvd_pos` + `mul_left_cancel_of_pos`, no case split on `k1`
  needed since `k1 ∣ k` and `k > 0` already force it) gives `k2 ∣ n`.
- **Reverse.** Fully uniform: `m*n = (k1*q1)*(k2*q2) = (k1*k2)*(q1*q2) =
  k*(q1*q2)` (a four-factor regroup, `mul_assoc` + `mul_left_comm`), no case
  split, works even when `k1` or `k2` is `0`.
- **`k=0` degenerate case: handled by DIRECT case split, not the general
  formula.** `h : dvd 0 (m*n)` gives `m*n=0` (`mul_eq_zero`), splitting into
  `m=0` (witnesses `(0,n)`) or `n=0` (witnesses `(m,0)`). This is exactly the
  corner the dispatching brief warned "a slick argument silently breaks" on:
  the general formula's `k2 := k/gcd(k,m)` does NOT reproduce a valid witness
  pair when `n ≠ 0 = m` — `gcd(0,m)=m`, `0/m=0`, forcing `k2=0` and needing
  `0 ∣ n`, false in general.

New file `crates/axeyum-lean-kernel/src/nat_prelude/dvd_mul_split.rs`, wired
in via one `declare_dvd_mul_split` call after `declare_gcd_mul_right_mirrors`/
`declare_dvd_add_iff_left`. **Not named `Nat.dvd_mul`**: that kernel name is
already taken by the unrelated trivial lemma `∀ a q, dvd a (a*q)`
(`nat_prelude.rs`'s pre-existing `dvd_mul` field) — declaring under Mathlib's
literal name would hit `DeclarationExists`, the `Nat.inverseIndex` collision
class. Named `dvd_mul_split` (checked free in both preludes before writing).

Detail moved to [`../notes/343-dvd-mul-split.md`](docs/plan/notes/343-dvd-mul-split.md).

**DONE (`countrange-bijection`, 2026-08-30).** Built and kernel-checked the
primitive `docs/plan/status/320-totient-bijection.md` named as the one
genuinely missing piece under `Nat.totient_mul_of_coprime`, plus both of the
other two pieces that lane's step (3) called for. **Five new theorems, no new
`Definition`, all axiom-free.** `nat_prelude::` **187 passed, 0 failed** (183
baseline + 4 new tests).

Of `320`'s three remaining steps toward `totient_mul_of_coprime`, step (2)
and the counting half of step (3) are now closed. What is left is step (1),
the CRT self-map's two hypotheses, and the final assembly — sized at the
bottom, with every ingredient named.

## The primitive

```text
Nat.countRange_permute :
  ∀ (f : Nat → Bool) (σ : Nat → Nat) (n : Nat),
    Nat.InjectiveOn σ n → Nat.MapsInto σ n →
    Eq Nat (countRange f n) (countRange (fun k => f (σ k)) n)
```

**Why this statement.** It is the exact `countRange` mirror of
`Int.prodRange_permute` — same hypotheses, same argument order — so the two
read against each other. It is also precisely what the CRT argument needs and
no more: for coprime `m, n` the map `g x := (x mod m) * n + (x mod n)` is an
injective self-map of `[0, m*n)`, and the coprimality predicate satisfies
`P x = Q (g x)` for **every** `x`, not merely `x < m*n` (checked numerically
for all `x < 60` at every `1 ≤ m,n ≤ 9`). So the consumer gets
`countRange Q (m*n) = countRange (Q ∘ g) (m*n)` from this theorem and closes
the last step with the *unconditional* `Nat.countRange_congr` that already
existed. No `P`/`Q` pair and no bounded pointwise agreement are needed in the
statement, so neither is in it.

## The other four

- **`Nat.countRange_product`** — the block/Fubini factorization, and the one
  step here that is **coprimality-INDEPENDENT**:

  ```text
  ∀ P R S n m,
    (∀ a b, Lt b n → R a = true  → P (add (mul n a) b) = S b) →
    (∀ a b, Lt b n → R a = false → P (add (mul n a) b) = false) →
    countRange P (mul n m) = mul (countRange S n) (countRange R m)
  ```

  Stated over an arbitrary `P` with two hypotheses pinning `R a` to each
  `Bool`, not over a fixed conjunction: this kernel exposes no `Bool`-valued
  `and` (`finite_set.rs`'s `bool_select_bool` is private), and a caller
  supplying its own combination discharges both by reduction. `Lt 0 n` is
  deliberately **not** a hypothesis — at `n = 0` both sides are `zero`, both
  hypotheses are vacuous, and the proof never divides.

Detail moved to [`../notes/344-countrange-bijection.md`](docs/plan/notes/344-countrange-bijection.md).

**Draw 6 is DECLINED, and that is the result.** ADR-0620 predicted it could
not satisfy R5 from un-owned modules; measured, it is worse — **zero**
coherent held-out-safe families exist, not one. Nothing was drawn:
`FAMILY_MODULES`, `FAMILY_ROUTES` and both manifests are untouched, no row
moved partition, no attestation count was raised, and `FROZEN UNCHANGED`
asserted directly with a negative control that fires.

R5 is hard-coded (`len(new_held_out) < 2` raises) and `PER_FAMILY = 10`, so
any draw needs **20 held-out-safe rows in two coherent families**. Of 2,155
drawable rows, 1,716 sit in modules an existing family already OWNS and are
unreachable; 11 un-owned modules reach the floor and **all 11 are over
mathematics a development or train family already publishes**. The un-owned
sub-floor remainder adjacent only to held-out is **7 rows spread over six
different questions** — not one family, let alone two.

Three corrections to ADR-0620, each re-derived here rather than carried
over ([ADR-0645](docs/research/09-decisions/adr-0645-draw-6-is-declined-there-is-no-held-out-safe-family-left.md)):

1. **A third proposer/generator divergence**, beyond the two already
   recorded: the two scripts carry different `HYGIENE` regexes. The
   generator also drops `.inj`/`.injEq`/`.noConfusion` and
   `Int.Linear.*`/`Nat.Linear.*`, collapsing `Init.Data.Int.Basic` 10 → **6**
   and `Init.Data.Int.Linear` 10 → **2**. The first is the only un-owned
   floor-height module whose mathematics is unpublished, so under the
   proposer's screen it looks exactly like the held-out family this draw
   needed. **The drawable ready set is 11**, not the proposer's 15 and not
   ADR-0620's 13.
2. **`instSubNat` opens nothing for blind breadth** — 285 extra drawable
   rows and **0** new un-owned ready modules — though ADR-0620 names it the
   cheapest route. It stays the right lever for dispatchable rows.
3. **`Nat.dist` and `Nat.nth` are the unblock.** They open
   `Mathlib.Data.Nat.Dist` (**18** rows, a metric on ℕ, no family names
   `dist`) and `Mathlib.Data.Nat.Nth` (**11**, the k-th satisfying index,
   none mentioning `Prime`) — exactly the two held-out families R5 demands.
   R9 name screen 0/18 and 0/11.

**Also blocking the next draw:** `mathlib-statable-vocabulary-v1.json` has
two writers. `gen-autogenesis-nursery-refill.py --check` has been RED on
`main` since 04:23 today, and its own advice — "regenerate without
`--check`" — would delete `bridge_provenance` and `row_digest` inside a
commit that looks like a draw. I did not run it that way.

Gates: holdout isolation `held_out=116 settled=0 references=0 PASS` exit 0,
unchanged; frontier exit 0, dispatchable **12**, byte-identical before and
after; `validate-facts.py` 2,220 facts, 0 errors, exit 0.

Detail, all measurements and both screens' numbers:
[`../notes/345-nursery-draw-6.md`](docs/plan/notes/345-nursery-draw-6.md).

**Done, 2026-08-30.** `F:ml430-int-dvd-mul-3a7b94cd` (`Int.dvd_mul`) closed.
`docs/plan/status/343-dvd-mul-split.md` (lane `dvd-mul-split`) had closed the
`Nat` sibling `F:ml430-nat-dvd-mul-ebd102e2` the same day and left a precise
three-item blocker list for the `Int` side. **All three were verified against
the tree rather than inherited, and two of the three turned out to be
unnecessary once the real content is routed through `natAbs` instead of a
signed `Int.gcd` scaling.**

## The three named prerequisites, checked

1. **"A general `Int.gcd_mul_right`."** Not built, and not needed. The
   handoff's own sketch scaled `Int.gcd` by a *signed* factor
   (`Int.gcd (x*z) (y*z) = Int.gcd x y * natAbs z`), which is exactly where
   the sign of the scaling factor has to be tracked. The proof here never
   does that: it converts the hypothesis and every intermediate fact to
   `natAbs` values up front (`nat_abs_dvd_nat_abs_of_dvd`, `nat_abs_mul`) and
   runs the whole real-content argument as a `Nat.gcd_mul_right` application
   over `natAbs c, natAbs a, natAbs b` — a genuinely `Nat`-level fact that
   already existed (lane `gcd-mul-right`, same day as `343`). Bridging back
   to `Int` divisibility happens exactly once, via `dvd_of_nat_abs_dvd`, at
   the very end.
2. **"An Int-level cancellation lemma for a nonzero common factor."** Also
   not built, also not needed, for the same reason: the one cancellation in
   the proof is `g1_nat*(natAbs w) ∣ g1_nat*nb ⟹ natAbs w ∣ nb`, a `Nat`-level
   fact, and `Nat.mul_left_cancel_of_pos` already applies once `g1_nat` is
   shown positive. A local Nat-level `dvd_cancel_left_of_ne_zero` — a
   straight copy of `nat_prelude/dvd_mul_split.rs`'s own
   `dvd_cancel_left_of_pos`, built from only `NatOps` default methods so it
   works verbatim from an `IntDev` context — is all that was needed.
3. **"Establishing `g1 ≠ 0` from `c ≠ 0`."** This one WAS a genuine gap, and
   it was cheap: `Nat.eq_zero_of_gcd_eq_zero_left` (already proved) plus a
   local copy of `ring.rs`'s private `nat_abs_zero_implies_int_zero`
   (`natAbs x = 0 → x = 0`, by `Int.rec`) compose directly into a fully
   constructive proof — no case split on `c`'s sign, no excluded middle
   beyond the single `c = 0 ∨ c ≠ 0` split the statement itself needs
   (`Int.eq_em`).

## The degenerate and negative cases

Detail moved to [`../notes/346-int-dvd-mul-split.md`](docs/plan/notes/346-int-dvd-mul-split.md).

**DONE.** `artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` had two
writers and the poorer one deleted `bridge_provenance` and `row_digest` at
exit 0, while the failing `--check` advised exactly that. The file now has one
owner, the red is cleared, and the shape is gated
([ADR-0652](docs/research/09-decisions/adr-0652-one-producer-per-key-a-generated-artifact-has-exactly-one-writer.md)).

**Why `--check` was red — it was right about staleness and wrong only about
the remedy.** The two producers agree **element for element** on `bridge` (72)
and `settled` (174), the whole substantive derivation. The refill generator's
document is a strict SUBSET: no `bridge_provenance`, no `row_digest`, none of
the four `bridge_*` coverage counts, shorter `derivation`. So the staleness was
real and was caused entirely by the second writer knowing less — the two never
disagreed about the mathematics. Reproduced at `main` in a `git archive` scratch
tree: sha `096d8c85` -> `27205641`, both keys gone, **exit 0**.

**Who owns it now.** `gen-autogenesis-statable-vocabulary.py`, alone.
`gen-autogenesis-nursery-refill.py` READS the artifact and cross-checks it
against its own independent derivation (constants from the pinned inventory's
`type_repr` rather than the cached constants file), raising instead of
overwriting on disagreement. `VOCABULARY` is out of its `outputs` map. Verified
both ways in a scratch tree: a real draw run leaves the file byte-identical;
a one-entry perturbation gives exit 1 naming the owning generator.

**What the new guard refuses** —
`scripts/check-generated-artifact-ownership.py`, ~10 s, 5 producers executed,
registered in **both** aggregate gates (`check-aggregate-scope.sh` green,
410/466 steps, 66 recorded differences, no new one):

| arm | refuses |
| --- | --- |
| `KEYS` | the artifact missing any key its owner derives, top level or nested |
| `KNOWN` | a script naming a guarded artifact that is not classified, or a classification the tree no longer matches |
| `READS` | a declared read-only script containing any write call (AST) |
| `RUNS` | a non-owner producer, EXECUTED in a sandbox, leaving it anything but byte-identical |
| `CTRL` | a RUNS arm that accepts a planted second writer |
| `OWNER` | an owner that cannot restore a perturbed copy byte for byte |

`RUNS` is empirical because the destroying write reached the path through a
dict value (`outputs = {VOCABULARY: …}` then `path.write_text(text)`), which
any receiver analysis a person would write misses. `KNOWN` derives its script
set from the tree, so a NEW writer goes red rather than unmeasured. The gate
classifies itself as a producer and bounds its own nesting.

Detail moved to [`../notes/347-vocab-two-writers.md`](docs/plan/notes/347-vocab-two-writers.md).

**Both declared; the screen now admits both modules at their predicted
counts.** ADR-0645/draw-6's notes measured the unblock as declaring two
kernel constants (`Nat.dist`, `Nat.nth`) so the R9 name screen admits
`Mathlib.Data.Nat.Dist` (18 rows) and `Mathlib.Data.Nat.Nth` (11 rows) —
exactly the two held-out-safe families a draw needs. Both landed.

- **`Nat.dist n m := add (sub n m) (sub m n)`** (`nat_prelude/dist.rs`) is
  Mathlib's own definition over our `sub`/`add` — same statement, so a later
  `ml430` mirror flip is honest. Landed with 7 theorems (`dist_comm`,
  `dist_self`, `dist_eq_sub_of_le[_right]`, `dist_zero_right`/`_left`,
  `dist_succ_succ`), each proved from lemmas already in the prelude
  (`sub_eq_zero_of_le`, `zero_le`, `sub_zero`, `add_zero`/`zero_add`,
  `add_comm`, `succ_sub_succ`) — no new induction needed.
- **`Nat.nth`** (`nat_prelude/nth.rs`) is deliberately NOT Mathlib's
  construction — Mathlib's is noncomputable, classically case-splitting on
  `Set.Finite (setOf p)`, and this kernel has neither `Set`/`Finset` nor
  `Classical.choice`. Built as an honest substitution in `Nat.minFac`'s
  style: `Nat.nthAux (dec : Nat -> Bool) (fuel k n : Nat) : Nat`, a
  fuel-bounded search over a decidable `Bool` predicate, using the same
  fuel/`Bool.rec` device `Nat.beq`/`Nat.land`/`Nat.sumRange` already use,
  generalized to two accumulators. `Nat.nth dec bound n := nthAux dec bound
  0 n`. Type differs from Mathlib's `(Nat -> Prop) -> Nat -> Nat`, so any
  `ml430` mirror against it stays open — documented in `nth.rs`'s module
  doc, following the `minFac`/`multichoose` precedent in `CLAUDE.md`.

Detail moved to [`../notes/348-nat-dist-nth.md`](docs/plan/notes/348-nat-dist-nth.md).

**DONE (`totient-mul-finish`, 2026-08-30).** `Nat.totient_mul_of_coprime`
landed, axiom-free, admitted by the kernel on the **first attempt**. Three new
theorems in a new file `nat_prelude/totient_mul.rs`, **no new
`Definition`**, two new hand-curated ledger facts. `nat_prelude::` **192
passed, 0 failed** (188 baseline + 4 new tests, one of which was the coverage
assertion firing correctly before the names were registered). `clippy
-p axeyum-lean-kernel --all-targets -- -D warnings` clean; `cargo fmt --all
--check` clean; `validate-facts.py` **2222 facts checked, 0 errors**.

```text
Nat.totient_mul_of_coprime :
  ∀ m n, Eq (gcd m n) 1 → Eq (totient (mul m n)) (mul (totient m) (totient n))
```

Proved **by counting** — no prime factorization, no Euler product, no Bézout
witness, and no CRT *existence* over ℕ anywhere in the term.

## Where the coprimality hypothesis actually goes

This is the shape of the result, and it is why the file states three theorems
rather than one. Run before any Rust, and extended afterwards for the mirrors:

```sh
python3 scripts/tests/check-totient-mul-coprime-numerics.py
```

26 checks, each paired with a negative control the script asserts must
*genuinely* fail. Over every pair with `1 ≤ m,n ≤ 9`:

| step | needs coprimality? | measured |
| --- | --- | --- |
| `Nat.crtSelfMap_mapsInto` | **no** | holds at all 81 pairs, incl. all 26 non-coprime |
| pointwise `P x = V (g x)` | **no** | holds for all `x < 60` at all 81 pairs |
| Fubini via `countRange_product` | **no** | holds at all 26 non-coprime pairs |
| `Nat.crtSelfMap_injectiveOn` | **YES** | holds at **0 of 26** non-coprime pairs |
| the theorem itself | **YES** | fails at **26 of 26** non-coprime pairs |

So the entire hypothesis is carried by one obligation. A single fused lemma
would have made it look load-bearing everywhere and hidden which step pays for
it, which is exactly the confusion `301`'s traced plan fell into.

The map, with `N = mul n m` (`n` the block WIDTH, `m` the block COUNT — the
shape `countRange_product` factors) and `V y := band (R (div y n)) (S (mod y n))`:

```text
g x := add (mul n (mod x m)) (mod x n)

countRange P (mul m n)                        -- totient (m*n), by δ
  = countRange P (mul n m)                    -- mul_comm, on the BOUND only
  = countRange (V ∘ g) (mul n m)              -- countRange_congr, UNCONDITIONAL
  = countRange V (mul n m)                    -- countRange_permute, run SYMM
  = mul (countRange S n) (countRange R m)     -- countRange_product
  = mul (totient m) (totient n)               -- mul_comm
```

Detail moved to [`../notes/349-totient-mul-finish.md`](docs/plan/notes/349-totient-mul-finish.md).

**Your lane's block (`DONE (both remaining facts closed --
clog_antitone_left, log2_eq_log_two; the 14-of-14 nat-log/nat-clog mirror
set started in 330-nat-log-mirrors.md is now complete)`, clog-log2-finish,
2026-08-30).**

Picked up from `docs/plan/status/337-log-clog-finish.md`'s handoff (12 of 14
`nat-log`/`nat-clog` mirrors closed there). This lane closed the remaining 2.

## Closed: 2 of 2

### `Nat.clog_antitone_left`

`Nat.clog_aux_antitone_base : ∀ f n a b, Le a b → Lt 1 a → Lt 1 b → Le
(clogAux b f n) (clogAux a f n)` in
`crates/axeyum-lean-kernel/src/nat_prelude/log_clog_order.rs`, mirroring
`log_aux_antitone_base` with the two guard cuts SWAPPED: `clogAux`'s outer
cut (`2 ≤ base`) is a pure base cut, individually known true from `ha`/`hb`
with no case split; its inner cut (`2 ≤ n`) is the SAME expression on both
sides (the value is fixed), needing exactly one case split instead of log's
two.

The `(n+b-1)`/`(n-1)+b` bridge **DID need a hypothesis** (`Le 1 n`) — the
handoff correctly flagged this. `Nat.sub` truncates: at `n = 0`, `sub(add(n,
base),1) = base - 1` while `add(sub(n,1),base) = base`, differing by exactly
one. New private helper `add_sub_one_swap` proves the bridge given `Le 1 n`
by reconstructing `n` as `succ (pred n)` via `succ_pred_of_pos` (passed
directly where `Lt 0 n` is expected — DEFEQ through `Nat.lt`'s definition,
the same subsumption `NatOps::zero_lt_succ`'s callers already rely on), then
cancelling the `succ` against the literal `1` on both sides via
`succ_add`/`succ_sub_succ`/`sub_zero`. A second helper, `ceil_div_succ_of_pos`,
composes this with the existing `Nat.add_div_right` to rewrite each side's
ceiling quotient to `(n-1)/base + 1`, turning the comparison into a floor
comparison at the shared numerator `n-1` (`div_le_div_left` +
`add_le_add_right`). From there the composition is `log_aux_antitone_base`'s:
IH at the SAME bases with the b-side's quotient, chained through
`clog_aux_mono` at the fixed base `a`, `le_trans`, then `le_succ_succ`.

`Nat.clog_antitone_left` is the diagonal `f := n`, exactly mirroring
`declare_log_antitone_left`.

### `Nat.log2_eq_log_two`

`Nat.log2` did NOT need a `WellFounded.fix` construction, contrary to two
prior handoffs' assessment (`330-nat-log-mirrors.md`'s original and
`337-log-clog-finish.md`'s repetition of it — **neither had actually read the
Lean source**). Read directly from the pinned toolchain
(`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Log2.lean`,
already provisioned on this host — `scripts/provision-lean-import-toolchain.sh
--verify` needs no network) before writing any code:

Detail moved to [`../notes/350-clog-log2-finish.md`](docs/plan/notes/350-clog-log2-finish.md).

**Draw 6 is DECLINED a second time, and the reason is new: the unblock
contaminated the family it opened.** Nothing was drawn — `FAMILY_MODULES`,
`FAMILY_ROUTES` and all three manifests are byte-identical to the
merge-base, no row moved partition, no attestation count was raised, and
`FROZEN UNCHANGED` is asserted directly with a negative control that fires.

ADR-0645 named `Nat.dist` + `Nat.nth` as draw 6's exact unblock and measured
`Mathlib.Data.Nat.Dist` at **R9 name screen 0 of 18**. That was measured
before `Nat.dist` existed. `nat_prelude/dist.rs` declares the definition
**and seven theorems**; five carry exact Mathlib mirror names in the Dist
pool, and two of them — `Nat.dist_comm`, `Nat.dist_self` — land in the
alphabetically-first ten a draw takes. **R9 is now 2 of 10.**

Measured against the real generator rather than argued — `select` + `guard`
run in memory, writing nothing:

    GUARD REFUSED: R9 2 held-out candidate(s) already have a declaration of
    the same Mathlib name in the kernel environment, so they are not blind:
    [('natural-distance', 'Nat.dist_comm'), ('natural-distance', 'Nat.dist_self')]

Control, same machinery, Dist moved to development: `GUARD PASSED -- 300
entries, 120 held-out`. So R9-on-Dist is the **single** mechanical blocker
and `Mathlib.Data.Nat.Nth` is fully held-out-safe (**R9 0 of 11**, whole
module 0 of 11 — the environment holds exactly `Nat.nth` and `Nat.nthAux`).

Selection is `pool[:PER_FAMILY]` over a name-sorted pool and `Nat.dist_comm`
sorts fourth, so no module tuple dodges it. Adding an environment screen
would let Dist draw ten clean rows of its thirteen — and would still be
wrong, because R9 is a proxy for the real rule that a blind family's
mathematics must be unpublished, and our own development has now proved a
quarter of `dist`. This is ADR-0542's natural-binomial shape caught at the
door instead of three days later.

R5 needs two held-out families. Of the other nine un-owned modules at the
floor, all nine are over mathematics a development or train family already
publishes — draws 2 through 5's exclusion list unchanged. The un-owned
sub-floor remainder is 136 rows across 52 modules and still several
unrelated questions, none reaching ten.

## Numbers re-derived for THIS draw, not carried

| quantity | ADR-0645 | this run |
| --- | --- | --- |
| env declarations | 2,207 | **2,374** |
| drawable (generator screens) | 2,155 | **2,295** |
| un-owned modules at the floor | 11 | **10** |
| proposer "ready families" | 15 | **17** (generator yields **10**) |

## The rule, and the unblock for draw 7

Detail moved to [`../notes/351-nursery-draw-6b.md`](docs/plan/notes/351-nursery-draw-6b.md).

**Your lane's block (`DONE (Nat.fermatNumber declared, definition and
evaluation test only; Mathlib.NumberTheory.Fermat now screens READY at
13/13, ready-family count 17 -> 18)`, nat-fermat-number, 2026-08-30).**

Dispatched per
[ADR-0653](docs/research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md):
draw 7 needs one more constant to reach the two new held-out-safe families
`check-dispatchable-frontier.py` requires, and `Nat.fermatNumber` was the
cheapest of the three measured there. The task was narrowly scoped on
purpose — ADR-0653 exists because a sibling lane's `Nat.dist` unblock
proved seven supporting theorems and spent the very family it opened.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number.rs` (new file):
`Nat.fermatNumber n := add (pow 2 (pow 2 n)) 1`, wired in as the LAST
`declare_*` call in `build_nat_prelude` (needs only `Nat.pow`/`Nat.add`,
both declared far above). Struct field `fermat_number: NameId` and its
constructor line added to `NatPrelude`; `p.fermat_number` added to
`nat_prelude_tests.rs`'s `definition_names` list so the environment-coverage
test (`every_nat_declaration_is_checked_and_axiom_free`) sees it.

**No theorem about it was declared** — per ADR-0653's rule, this is the
entire point of the task.

### Mathlib's actual definition, read at the pinned toolchain

`scripts/provision-lean-import-toolchain.sh --verify` (needs no network,
~instant since already provisioned):

```
LEAN_IMPORT_TOOLCHAIN|mathlib=c5ea00351c28e24afc9f0f84379aa41082b1188f|...|verdict=PASS
```

`/data0/axeyum/lean-import-toolchain/mathlib4/Mathlib/NumberTheory/Fermat.lean:34`:

```
def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1
```

Single explicit `Nat` argument, base `2` fixed, nested exponent. Confirmed
against the file directly rather than inferred from ADR-0653's paraphrase.

### Hand-computed evaluation values, and their cost

`fermatNumber 0 = 2^(2^0)+1 = 2^1+1 = 3`
`fermatNumber 1 = 2^(2^1)+1 = 2^2+1 = 5`
`fermatNumber 2 = 2^(2^2)+1 = 2^4+1 = 17`

Detail moved to [`../notes/352-nat-fermat-number.md`](docs/plan/notes/352-nat-fermat-number.md).

**Status: DONE. The draw is authored and
[`check-dispatchable-frontier.py`](scripts/check-dispatchable-frontier.py)
is GREEN — 4 dispatchable before, 24 after, against a floor of 10.**

Decision record:
[ADR-0654](docs/research/09-decisions/adr-0654-draw-7-is-authored-and-the-lawful-family-set-was-forced-not-chosen.md).
Measurements and reproducible probes: [`../notes/353-nursery-draw-7.md`](docs/plan/notes/353-nursery-draw-7.md).

Draw 6 was declined twice and both declines were right — ADR-0645 because no
held-out-safe family existed, ADR-0653 because the lane that declared the
unblocking constant `Nat.dist` also proved five exact Mathlib mirror names, two
inside the first ten a draw takes. `Nat.fermatNumber` has since landed, which is
the third unblock ADR-0653 measured, and with it a draw exists.

## The family set was forced, not chosen

Enumerating all subsets of the eleven un-owned modules at the `PER_FAMILY`
floor: a subset is lawful iff every cycle position congruent to 0 mod 3 is
held-out-safe and R5's two-family minimum holds. **Exactly one survives.**

| primary module | family | partition | rows |
| --- | --- | --- | --- |
| `Mathlib.Data.Nat.Nth` | `natural-nth-selector` | **held-out** | 10 of 11 |
| `Mathlib.Data.Nat.Prime.Basic` | `natural-prime-arithmetic` | development | 10 of 29 |
| `Mathlib.Data.Nat.Prime.Defs` | `natural-prime-characterizations` | train | 10 of 29 |
| `Mathlib.NumberTheory.Fermat` | `fermat-numbers` | **held-out** | 10 of 13 |

Only two modules are held-out-safe; Fermat sorts last of all eleven so it must
take index 3, which fixes `n = 4`, puts Nth at index 0, and leaves the two Prime
modules as the only things sorting between them. The Prime families are lawful
because they are **not blind** — v1 `natural-primes` is development, and
ADR-0653 states the rule for exactly that case.

`Mathlib.Data.Nat.Dist` is **not** drawn, against ADR-0653's closing
recommendation: it sorts before Nth, so including it either lands it at held-out
(R9 refuses) or displaces Fermat. Forced, not overlooked.

## Both screens, both held-out families

| family | screen 1 (R9, exact name) | screen 2 (namespace, any name) |
| --- | --- | --- |
| `fermat-numbers` | **0/10**, whole module 0/13 | 1 declaration — `Nat.fermatNumber` |
| `natural-nth-selector` | **0/10**, whole module 0/11 | 2 — `Nat.nth`, `Nat.nthAux` |

Positive controls in the same run so a misfiring screen cannot look clean:
`Nat.dist` 8 (the contaminated family), `Nat.gcd` 17, `/[Pp]rime/` 65,
`/dist/i` 40. The sweeps also make ADR-0653's construction-only rule
**measurable** — the `fermatNumber` lane declared the construction and nothing
else, and it shows as a sweep of one.

## Gates

Detail moved to [`../notes/353-nursery-draw-7.md`](docs/plan/notes/353-nursery-draw-7.md).

**Your lane's block (`DONE`, modeq-add-le, 2026-08-30).**

Closed the one fact `docs/plan/status/329-nat-modeq-mirrors.md` left open:
`F:ml430-nat-modeq-add-le-of-lt-c774015b`
(`Nat.ModEq.add_le_of_lt : a ≡ b [MOD m] → a < b → a + m ≤ b`).

## What the prior handoff got wrong about its own blocker

`329-nat-modeq-mirrors.md` sized this fact as needing "2-3 new
order/monotonicity lemmas" before the modEq-specific argument could even
start: an `Lt`-to-existence bridge (to extract witnesses from `a < b`) and a
`m*u > m*v → u > v` cancellation. Verifying in-tree found **neither was
needed**:

- This prelude's `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v`
  (`nat_prelude/modular.rs`) is already an existence form — the hypothesis
  *hands over* witnesses `u, v` directly via `exists_rec`. There is nothing
  to bridge; `a < b` is used as-is (see below), not converted into a
  witness.
- `Nat.lt_of_mul_lt_mul_left : ∀ a b c, Lt (mul a b) (mul a c) → Lt b c`
  (`nat_prelude/mul_order_lemmas.rs`) already **is** the cancellation, and
  it needs no positivity side-condition — the handoff's guess that this was
  missing was exactly backwards: it was declared and tested (with a
  discriminating numeral instance) before this lane ever started.

So the fact closed with **zero new order/monotonicity lemmas** — only a
proof term composing what already existed.

## The proof (new file `crates/axeyum-lean-kernel/src/nat_prelude/modeq_add_le_of_lt.rs`)

Given witnesses `u, v` with `a + m*u = b + m*v` (destructured from the
hypothesis via the standard double-`exists_rec` idiom already used
throughout `modular.rs`) and `a < b`:

Detail moved to [`../notes/354-modeq-add-le.md`](docs/plan/notes/354-modeq-add-le.md).

**DONE (`totient-prime-power`, 2026-08-30).** Six theorems landed in a new
file `nat_prelude/totient_prime_pow.rs`, **all six admitted by the kernel on
the first attempt**, all axiom-free, no new `Definition`. `nat_prelude::`
**201 passed, 0 failed** (196 baseline + 4 new tests + the coverage assertion,
which fired correctly before the names were registered). `cargo fmt --all
--check` clean; `clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
clean; `validate-facts.py` **2225 facts, 0 errors**;
`scripts/gen-adr-index.py` exit 0.

```text
Nat.countRange_const_true          ∀ n, countRange (fun _ => true) n = n
Nat.coprime_mul_iff_of_dvd         e ∣ m → (gcd k (m*e) = 1 ↔ gcd k m = 1)
Nat.totient_mul_of_dvd             e ∣ m → φ(m*e) = φ(m)*e
Nat.totient_pow_succ_of_prime      Prime q → φ(q^(j+1)) = (q-1)*q^j
Nat.totient_prime_pow              Prime q → φ(q^(j+1)) = q^(j+1) - q^j
Nat.totient_dvd_totient_mul_prime  Prime q → φ(x) ∣ φ(x*q)
```

Three hand-curated ledger facts: `F:nat-totient-mul-of-dvd`,
`F:nat-totient-prime-pow`, `F:nat-totient-dvd-totient-mul-prime`.

## The assessment the task asked for first

**All three remaining `ml430` mirrors are reachable WITHOUT multiset
uniqueness.** The Euler-product route needs it; a prime-peeling induction does
not, and that is the finding — recorded as
[ADR-0668](docs/research/09-decisions/adr-0668-the-totient-mirrors-do-not-need-multiset-uniqueness.md)
with the full argument and the simulated inductions.

This **corrects** `349`'s sizing. That lane wrote that both mirrors "need the
non-coprime formula, which needs a totient value at prime powers plus a
product over a factorization" — right about the *Euler-product route*, and it
reads as a statement about the *targets*. It is the standing failure mode this
repository has now hit three times: a handoff reports accurately on its own
route, and the route-local blocker gets promoted into a claim about the goal.

Why uniqueness drops out, in one sentence: each target is **preserved along a
chain of prime steps**, the chain is built from *some* factorisation of the
cofactor, and nothing ever compares two factorisations — so nothing needs them
to agree. Uniqueness is required only to *evaluate* a closed-form product,
which none of these arguments does.

The only number-theoretic inputs are `Nat.exists_prime_dvd` (every `n > 1` has
a prime divisor — far weaker than unique factorisation), `Nat.euclid_lemma`,
`Nat.gcd_mul_right`, and the prime step. **All four now exist.**

## Numeric checks, as re-executable commands

Detail moved to [`../notes/355-totient-prime-power.md`](docs/plan/notes/355-totient-prime-power.md).

**DONE (`prime-dvd-mirrors`, 2026-08-30).** 14 of 19 dispatchable `ml430`
prime-divisibility facts closed. New file `nat_prelude/prime_dvd_mirrors.rs`
declares 13 theorems, **all admitted by the kernel on the first attempt**, all
axiom-free, no new `Definition`:

```text
Nat.prime_one_lt                    Prime p -> 1 < p
Nat.prime_one_le                    Prime p -> 1 <= p
Nat.prime_pos                       Prime p -> 0 < p
Nat.prime_ne_one                    Prime p -> p != 1
Nat.prime_ne_zero                   Prime p -> p != 0
Nat.prime_not_dvd_one               Prime p -> ~(p | 1)
Nat.prime_eq_one_or_self_of_dvd     Prime p -> m | p -> m = 1 \/ m = p
Nat.prime_dvd_iff_eq                Prime p -> a != 1 -> (a | p <-> p = a)
Nat.prime_dvd_mul_iff               Prime p -> (p | m*n <-> p|m \/ p|n)
Nat.prime_coprime_iff_not_dvd       Prime p -> (gcd p n = 1 <-> ~(p|n))
Nat.prime_eq_two_or_odd             Prime p -> p = 2 \/ Odd p
Nat.prime_eq_two_or_mod_two_eq_one  Prime p -> p = 2 \/ p%2 = 1
Nat.prime_mod_two_eq_one_iff_ne_two Prime p -> (p%2=1 <-> p != 2)
Nat.prime_coprime_pow_of_not_dvd    Prime p -> ~(p|a) -> gcd a (p^m) = 1
```

A 14th fact, `F:ml430-nat-prime-dvd-or-dvd-4ae88221`, was flipped WITHOUT a
new declaration: its statement is `Nat.euclid_lemma` (`bezout.rs`) verbatim up
to bound-variable names, so its checker cites `euclid_lemma` directly — no
`Nat.prime_dvd_or_dvd` declaration exists and none should be added.

`primes.rs`: `prime_condition` and `prime_parts` made `pub(super)` so the new
file reuses the primality spelling (`2 <= p /\ forall c, c|p -> c=1 \/ c=p`)
rather than re-deriving it.

Checks run: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — **203
passed, 0 failed** (202 baseline + 1 new statement-shape test). `cargo fmt
--all --check` clean on touched files (formatted individually with `rustfmt
--edition 2024`, not workspace `cargo fmt`). `cargo clippy -p
axeyum-lean-kernel --all-targets -- -D warnings` clean. `python3
scripts/validate-facts.py`: **2265 facts, 0 errors**.

Detail moved to [`../notes/356-prime-dvd-mirrors.md`](docs/plan/notes/356-prime-dvd-mirrors.md).

**DONE (`prime-char-mirrors`, 2026-08-30), CORRECTED AFTER A DISPATCH
COLLISION.** This lane was scoped as "everything in the
`Mathlib.Data.Nat.Prime.Defs` characterization family except five named
facts", which the sibling `prime-dvd-mirrors` lane was assigned. That
sibling went on to declare **fourteen** facts, not five, and landed on
`main` first. Nine of this lane's fifteen original declarations were
exact `NameId` collisions (`DeclarationExists` on merge); a tenth,
`F:ml430-nat-prime-eq-two-or-odd-44a91651`, was a duplicate PROOF of the
same fact under a different Rust name
(`prime_eq_two_or_mod_two_eq_one` vs this lane's
`prime_eq_two_or_odd_mod`) — no compile collision, but pointless
duplication once the sibling's version was already on `main`.

**Surviving from this lane, in `nat_prelude/prime_char.rs`: 5 facts.**

```text
Nat.prime_not_prime_pow_two_le   2<=n -> ~Prime(x^n)
Nat.prime_not_prime_pow_ne_one   n!=1 -> ~Prime(x^n)
Nat.prime_eq_one_of_pow          Prime(x^n) -> n=1
Nat.prime_not_coprime_iff_dvd    ~Coprime m n <-> exists p, Prime p /\ p|m /\ p|n
Nat.prime_mul_eq_prime_sq_iff    Prime p -> x!=1 -> y!=1 -> (x*y=p^2 <-> x=p /\ y=p)
```

The other ten (`prime_one_le`, `prime_pos`, `prime_one_lt`,
`prime_ne_zero`, `prime_ne_one`, `prime_not_dvd_one`,
`prime_eq_one_or_self_of_dvd`, `prime_eq_two_or_odd`,
`prime_eq_two_or_odd_mod`/`prime_eq_two_or_mod_two_eq_one`,
`prime_mod_two_eq_one_iff_ne_two`) are the sibling's, in
`nat_prelude/prime_dvd_mirrors.rs` — untouched, fact files left exactly
as `main` had them (`git checkout --theirs`), never re-flipped.

`nat_prelude::` **203 passed, 0 failed** (`main`'s post-collision
baseline, unchanged in count since nothing here adds a new theorem name
`main` doesn't already have — the surviving 5 were already counted).
`every_nat_declaration_is_checked_and_axiom_free` and
`the_nat_prelude_declares_no_axioms` both pass. `cargo clippy -p
axeyum-lean-kernel --all-targets --all-features -- -D warnings` and
`cargo fmt --all --check` both clean. `validate-facts.py`: **2265
facts, 0 errors** after `check-fact-depends-derived.py --fix`.

## What the merge actually required (for whoever reads this next)

Detail moved to [`../notes/357-prime-char-mirrors.md`](docs/plan/notes/357-prime-char-mirrors.md).

**DONE (`totient-dvd-chain`, 2026-08-30).** Both facts assigned to this lane
closed axiom-free, first attempt after fixing bugs found via
`Kernel::render_lean`-based debugging (never by hand-tracing to the end):

    F:ml430-nat-totient-dvd-of-dvd-9622e44a            a | b -> totient a | totient b
    F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7  a | b -> totient a = totient b
                                                          -> a = b \/ 2*a = b

Four new theorems landed in a new file `nat_prelude/totient_dvd_chain.rs`:

```text
Nat.totient_dvd_totient_mul     forall k a, Dvd (totient a) (totient (mul a k))
Nat.totient_dvd_of_dvd          Dvd a b -> Dvd (totient a) (totient b)
Nat.totient_mul_cofactor_bound  Le 1 (totient a) -> Le 2 k ->
                                 Or (Le (2*totient a) (totient (a*k)))
                                    (And (k=2) (totient (a*k) = totient a))
Nat.eq_or_eq_of_totient_eq_totient  Dvd a b -> totient a = totient b ->
                                     Or (a=b) (2*a=b)
```

`nat_prelude::` **206 passed, 0 failed** (202 baseline + 4 new tests).
`cargo fmt --all --check` clean (checked via `-p axeyum-lean-kernel`);
`clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean;
`validate-facts.py` **2265 facts, 0 errors**;
`scripts/check-fact-depends-derived.py --fix` applied cleanly to the second
fact (12 direct-lemma edges added).

## ADR-0668's claim: did "only the induction remains" hold?

**Yes, for Target 1 outright; yes for Target 3 with one addition ADR-0668
did not spell out precisely enough to skip verifying.**

Target 1 needed exactly what the ADR named: a well-founded induction on the
cofactor `k := b/a`, chaining `Nat.totient_dvd_totient_mul_prime` along a
prime peeled one at a time by `Nat.exists_prime_dvd`. No new number theory.

Detail moved to [`../notes/358-totient-dvd-chain.md`](docs/plan/notes/358-totient-dvd-chain.md).

**Status: DONE.** Measurement task, not a build task. **No fact was
reclassified, reopened or edited.**

## The answer

The Pareto claim holds **for IVT** and **not for EVT**.

| ADR-0603 row | IVT | EVT |
| --- | --- | --- |
| 1 general constructive | `CReal.ivt_approx` — genuine | **ABSENT** (`CReal.supOn` not in the environment) |
| 2 boundary refutation | `CReal.ivt_exact_root_decides_sign` — survives a harsh reading | `CReal.evt_attained_max_decides_sign` — theorem sound, ledger evidence thin |
| 3 decidable fragment | CAS; substantive half is `cas-internal` | CAS; substantive half is `cas-internal` |
| 4 labeled import | **ABSENT** | **ABSENT** |

EVT is a refutation of the classical statement with nothing constructive
standing in its place, so it is a trade rather than a dominance:
Mathlib's `IsCompact.exists_isMaxOn` proves EVT for an arbitrary compact subset
of an arbitrary topological space and we prove nothing positive at all.
`creal/supremum.rs` already says `CReal.supOn` is "still not landed"; nothing in
the ledger or in `07-the-cost-model-and-pareto-position.md` records that EVT is
being cited as a dominance example while its row 1 is missing.

## Deliverables

- Audit: `docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`
- Decision: `docs/research/09-decisions/adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md`
- Instruments committed beside them: `scratch-probe.sh`, `scratch-ivt-dump.py`,
  and the raw `scratch-inventory.txt` / `scratch-ivt-types.txt` they produced.

## Also found

Detail moved to [`../notes/359-ivt-evt-pareto.md`](docs/plan/notes/359-ivt-evt-pareto.md).

## Status

**`CReal.supOn` LANDED**, derived and axiom-free, with
`CReal.supSeq_converges_supOn` tying it to the mesh maxima it is built from.
Thirteen declarations, four rungs. Twelve were first-attempt kernel accepts;
the thirteenth failed once on a `pi_fv`/`arrow` binder. Decision recorded in
[ADR-0691](docs/research/09-decisions/adr-0691-supon-lands-evt-gets-a-row-one-but-not-yet-the-lub-laws.md).

This answers [ADR-0675](docs/research/09-decisions/adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md)'s
finding that EVT had a row-2 impossibility result with nothing constructive
behind it. **It does not yet restore per-statement dominance** — see "What is
still open" below, which is the part to read before quoting this lane.

### Landed

In `crates/axeyum-lean-kernel/src/creal/supremum.rs`:

| rung | declarations |
| --- | --- |
| 6c | `CReal.meshLevelCount_ge_of_size` |
| 6d | `CReal.meshMax_le_add_of_modulus` |
| 6e | `CReal.supLevel`, `CReal.supLevel_mono`, `CReal.supSeq`, `CReal.supSeq_mono`, `CReal.supSeq_le_add` |
| 6f | `CReal.le_meshLevelCount`, `CReal.supSeq_abs_diff_le`, `CReal.supSeq_cauchy` |
| 7 | `CReal.supOn`, `CReal.supSeq_converges_supOn` |

Plus one extraction in `creal/ivt.rs`: `CReal.scaledCauchy_of_abs_diff_le`,
the raw `(K+2, per-pair)` pair that `cauchy_of_abs_diff_le` already built and
then immediately hid inside an `Exists`. `regular_of_scaled_cauchy` needs it as
DATA and kernel fact 2 means a `Cauchy f` witness can never give it back.

### Verification

- `creal_prelude_builds`: **110.4 s before, 114.0 s after** — flat. (An
  intermediate 143.8 s reading was contention, load 9.3 with a sibling lane's
  `rustc` at 436% CPU; it did not reproduce.)
- Full `creal::` sweep: **199 passed, 0 failed.** This includes
  `every_creal_declaration_is_checked_and_axiom_free`, which enumerates
  `kernel.environment()` rather than a hand list — so it is what confirms all
  thirteen are derived and axiom-free, and it is what caught them being absent
  from the inventory shards.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
  `rustfmt --check` on every touched file: clean.
- Not run: the workspace gate, `check.sh`, and `prelude_theorem_inventory`.
  The coordinator re-verifies. Note that the theorem inventory would not have
  answered the question anyway — `supOn` is a `Definition`, and that tool lists
  theorems only.

## What is still open — read this before claiming EVT dominance

`supOn` is **a value with a convergence law, not yet a characterized
supremum.** Every machine-checked statement about it currently says only that
it is the limit of the mesh maxima. Two declarations separate that from EVT:

Detail moved to [`../notes/360-creal-supon.md`](docs/plan/notes/360-creal-supon.md).

**Status: DONE.** Follow-up to lane 359's audit
(`docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md`,
ADR-0675), which found three ledger-quality problems and deliberately left
them unfixed. This lane fixed them.

## 1. Nine (measured: ten) generated-unreviewed CReal IVT/EVT facts, curated

The audit and its own brief both said "9 of 11". Recounted directly from
`provenance.curation`: **10 of the 11 CReal IVT/EVT facts were
`generated-unreviewed`**, not 9 — the audit's "9 constructive + 2 row-2" split
is right, but only one of the two row-2 facts
(`F:creal-ivt-exact-root-decides-sign`) was curated; the other
(`F:creal-evt-attained-max-decides-sign`) was still generated-unreviewed too.
All ten are now curated, reading from the rendered kernel type plus the module
documentation in `creal/ivt.rs`, `creal/ivt_boundary.rs`, `creal/extreme_value.rs`
and the field docs in `creal.rs`:

| fact | before | after (one line) |
| --- | --- | --- |
| `F:creal-ivt-approx` | boilerplate, no characterisation | ADR-0603 row 1, the real general form: arbitrary `F`/`a`/`b`, `∀n` accuracy — but fixed target 0, fixed orientation, uniform (not pointwise) continuity |
| `F:creal-ivt-step` | boilerplate | one bisection step; weak epsilon-slack invariant, never decides an exact sign |
| `F:creal-ivt-iter` | boilerplate | `n`-fold bisection, width shrinks geometrically; still pure machinery |
| `F:creal-ivt-bisect-invariant` | boilerplate | the computable (data) bracket satisfies the same 6-part invariant as the existential one — what makes a sequence possible at all |
| `F:creal-ivt-bisect-approx` | boilerplate | `ivt_approx`'s bound restated at a named point instead of an existential witness |
| `F:creal-ivt-bisect-cauchy-bound` | boilerplate | real-valued Cauchy estimate between two accuracies, needs the stronger derivative hypothesis |
| `F:creal-ivt-bisect-cauchy` | boilerplate | the named-point sequence is a genuine `CReal.Cauchy` sequence |
| `F:creal-ivt-exact-root` | boilerplate | EXACT root, priced at a uniformly positive derivative on the whole interval — strictly stronger than Mathlib's `ContinuousOn`, and row 2 shows nothing weaker will do |
| `F:creal-ivt-exact-root-at` | boilerplate | same exact-root theorem generalized to an arbitrary target `y`, same strong hypothesis |
| `F:creal-evt-attained-max-decides-sign` | boilerplate | EVT's row 2: an attained maximiser for a linear family decides the sign of an arbitrary real — and, stated explicitly for the first time in this fact, EVT has **no** positive constructive form behind it anywhere in the ledger (unlike IVT) |

Detail moved to [`../notes/362-ivt-evt-ledger-hygiene.md`](docs/plan/notes/362-ivt-evt-ledger-hygiene.md).

**Status:** complete. Read-only audit lane; it wrote only its own report and
controls, and edited no fact, proof or gate.

**Deliverable:** [`docs/research/11-design-review/2026-08-30-session-audit.md`](docs/research/11-design-review/2026-08-30-session-audit.md).

## What it found

Nine claims refuted or shown unverifiable, five gate guards shown to be
survivors, and four headline claims that survived attack.

The three that most change what may be said out loud:

1. **`natural-parity` (10 held-out rows) was never blind.**
   `Nat.even_iff_mod_two_eq_zero` landed five hours before the family was
   preregistered held-out. Identical in shape to the `natural-divisibility`
   amendment made today; undiagnosed. A further **3 of 10** `fermat-numbers`
   rows were established in-tree 21 minutes before draw 7 preregistered them —
   an evaluation test asserts exactly those three propositions by `def_eq` and
   names the Mathlib lemmas in its doc comment.
2. **"IVT is Pareto-dominant" overstates the audit it rests on.** That document
   records three axes where Mathlib wins, one of them "real and permanent", then
   applies a strict dominance test to EVT and a loose one to IVT. Applied
   consistently, IVT is *mutually non-dominated*, not dominant — and its
   dominance failure is the permanent one while EVT's is fixable.
3. **Five gate guards are survivors**, including every guard in
   `check-merge-hygiene.sh` (landed today with zero registered mutation
   controls) and `check-aggregate-scope.sh`'s fail-on-new-divergence guard,
   which can be replaced with `if false` while its registered controls stay
   green.

## What survived

The excluded-middle unprovability result (eleven `Provable` constructors read
out of the kernel environment are exactly the IPC natural-deduction rule set;
`Formula` has no `top`; strict positivity is checked; 50 declarations
axiom-free; the checker discriminates in both directions),
`Nat.totient_mul_of_coprime` (coprimality load-bearing and pinned by an
`m = n = 2` negative control, numerics re-run rather than inherited), the
per-prelude axiom table measured on a freshly built binary with four fail
directions tested, and the ledger histogram re-derived independently twice.

## Follow-on work this lane deliberately did not do

Amending `natural-parity` and the three `fermat-numbers` rows (ADR-0542 repair
is by amendment, never deletion); registering mutation controls for
`check-merge-hygiene.sh`; ratcheting `check-cas-substance.py`'s headline count;
fixing `strip_wrappers`' quote-blind split in `check-aggregate-scope.sh`; adding
`hooks/*` to the shell-antipattern scan. Each belongs to a lane that may write.

## Status

DONE. Two more held-out families amended out under ADR-0542, both verified
independently before anything was written; both of today's contamination shapes
made detectable; ADR-0695 resolves the evaluation-test tension.

**Blind population: 116 held-out rows across 12 families**, out of 300 rows in
`nursery-v2-extension.json` plus 214 in `nursery-v1.json`. Composition 16 in
v1, 100 in the extension.

```
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|settled=0|
  references=0|verdict=PASS                                       REAL EXIT=0
HOLDOUT_CLOSED_EVALUATION|held_out=116|closed_shaped=0|violations=0|
  snapshot_declarations=2383|fixtures=10|verdict=PASS             REAL EXIT=0
```

## Both findings, re-derived

`git log -1 -S` gives the NEWEST commit touching a string, so every date is
from `git log --reverse -S` with the order confirmed by
`git merge-base --is-ancestor`.

**`natural-parity`, all 10 rows, never blind.** Preregistered held-out at
2026-08-29 17:22:14 (`94b3e61ee`). `Nat.even_iff_mod_two_eq_zero` —
`∀ n, Iff (Even n) (Eq (mod n 2) 0)`, which is `F:ml430-nat-even-iff-024826e9`
verbatim, over the `Even n := ∃ k, n = k + k` that is Mathlib's own definition
— admitted 2026-08-29 12:10:13 (`414eef0a2`). Five hours twelve minutes.

*Correction to the brief*: it dated the preregistration 2026-08-30 00:57. That
commit (`6f4b1e62b`) only ADDED the duplicate `preregistered_family_partitions`
block, which is why a `-S` search reports it. The preregistration is
`94b3e61ee`, matching the audit.

The audit's claim about the other nine holds. Seven have an admitted Int
sibling one carrier transport away — `Int.odd_of_mul_left`,
`Int.odd_of_mul_right`, `Int.ediv_two_mul_two_of_even`,
`Int.ediv_two_mul_two_add_one_of_odd`, `Int.even_add`, `Int.even_add_prime`,
`Int.even_add_one` — all wired into `int_prelude.rs:1903-1918`, plus the bridge
`Int.even_iff_nat_abs_even`. Only `add_one_lt_of_even` and `even_div` have
none. And `int_prelude/parity.rs:199-202` states in its own module doc that it
builds the **Nat-level** content of the two `odd_of_mul` rows inline from
`right_distrib`/`left_distrib` "since neither has a home in `nat_prelude` yet"
— hiding place 2, invisible to any name index.

Detail moved to [`../notes/364-holdout-amendment-2.md`](docs/plan/notes/364-holdout-amendment-2.md).

## Status

**LANDED.** All five gates named in
[the 2026-08-30 session audit](docs/research/11-design-review/2026-08-30-session-audit.md)
§5b now have controls that die when the guard dies. Every kill set below is as
measured by `scripts/tests/mutation_controls.py`, survivors included.

The standing rule this lane worked to: **a gate is not made green by making it
blind.** Two gates gained new failure modes (a ratchet, a scope assertion) and
both were driven to red on purpose before being recorded green.

### 1. `check-merge-hygiene.sh` — zero controls, and its exemption covered every control suite

It landed the same day with **no registered controls**, so every guard in it was
a survivor by definition. Ten scenarios now drive the shipped script against a
throwaway git tree (`AXEYUM_MERGE_HYGIENE_ROOT`, the `AXEYUM_KERNEL_SUITES_ROOT`
device); nothing is re-implemented.

Two defects fixed alongside, both reported by the audit:

- the conflict-marker pathspec excluded `scripts/tests/*` — **every control
  suite in the repository** — from the marker guard. Narrowed to
  `scripts/tests/fixtures/*`. Measured before narrowing: zero tracked files
  under `scripts/tests/` contain a marker, so it cost nothing. The new suite
  therefore *builds* its marker text from repeated characters rather than
  writing it literally, so it is scanned by the guard it tests.
- the header said "the four things" while the body gives a reasoned explanation
  for enforcing three.

| mutant | killed |
| --- | --- |
| M1 conflict-marker branch | 4 |
| M2 bare `=======` alternative | 1 |
| M3 `fixtures/` exemption, not the whole directory | 1 |
| M4 ADR-index branch | 3 |
| M5 the ADR checker's own output is reported | 1 |
| M6 `gen-plan` branch | 2 |

No survivors. M1/M4/M6 kill more than one because each is **one** `if` reached
by several scenarios; a suite in which they died separately would be testing
branches that do not exist.

### 2. `check-aggregate-scope.sh` — an untested failure path and a live phantom class

`if [ -s "$new" ]; then` → `if false; then` left the registered suite green
(`AGGREGATE_SCOPE_CONTROLS|guards=5|negative_controls=2|PASS`, exit 0), because
all five registered controls test the **normalizer**.

`test-check-aggregate-scope.sh` keeps that job. The new suite drives the gate
end to end on a synthetic tree via `AXEYUM_AGGREGATE_SCOPE_ROOT` — hermetic,
because the real tree costs 413 + 469 steps to enumerate and because the
zero-side refusal cannot be reached on it at all.

The phantom: `strip_wrappers` *tested* for a leading environment assignment with
a quote-aware regex and *stripped* it with `line.split(" ", 1)`, which cuts at
the first space — inside the quotes.

Detail moved to [`../notes/365-gate-survivors.md`](docs/plan/notes/365-gate-survivors.md).

## Status

**Done.** Adjudicated the adversarial audit's charge
([`2026-08-30-session-audit.md`](docs/research/11-design-review/2026-08-30-session-audit.md)
§Part 1 item 3) that
[`08-ivt-and-evt-measured-against-mathlib.md`](docs/formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
graded IVT and EVT on inconsistent criteria.

**The charge holds against the presentation, not against the verdict.** No
test was written down before §4's axis tables were built, so the "Net" lines
read as an unweighted vote over an ad hoc axis list — three Mathlib-wins
excused for IVT, one comparable Mathlib-win sinking EVT, with no stated rule
for the difference. But `07-the-cost-model-and-pareto-position.md` §1
already states the real test, narrower than the seven-axis table: dominance
is decided by exactly two axes — **trusted base** (axiom footprint) and
**computational content** (constructive-with-a-program vs
classical-existence) — on a statement we ship that is comparable to
Mathlib's; breadth (generality of statement, of structure, which continuity
notion is assumed) is **explicitly conceded**, per that same section, never
scored toward or against the verdict. That test was simply never carried
into the comparison document.

Applied uniformly:

Detail moved to [`../notes/366-ivt-claim-correction.md`](docs/plan/notes/366-ivt-claim-correction.md).

## Status

**LANDED.** `scripts/check-control-registration.sh`'s G2 rejected four
hyphenated `.py` scripts under `scripts/tests/` on the stated reason that a
hyphenated name "is not an importable module so `python3 -m unittest
scripts.tests.<name>` cannot run it either." **That half of the reasoning is
false, measured directly**, and the fix replaces the blanket rejection with a
reachability check.

### The real mechanism (measured, not inherited)

    python3 -m unittest scripts.tests.check-totient-prime-power-numerics
    -> exit 0, prints all 37 checks, but NO "Ran N tests" line anywhere

    python3 -m unittest scripts.tests.definitely_not_a_module_zzz
    -> exit 1, ModuleNotFoundError (the loader's own __import__ call)

    python3 -c "importlib.import_module('scripts.tests.check-totient-prime-power-numerics')"
    -> exit 0, identical output, NO unittest involved at all

`__import__`/`importlib.import_module` resolve a dotted path by matching file
names on disk; the identifier restriction that forbids a hyphen belongs to the
`import` *statement*'s parser, not to programmatic import. So the hyphenated
file genuinely **does** import under `python3 -m unittest scripts.tests.<name>`
— the guard's premise was wrong. What actually happens is stranger than "runs
as a test": none of the four scripts is a `unittest.TestCase`; each is a
standalone script that calls `sys.exit(0)`/`sys.exit(1)` at module level, so
the *import itself* terminates the whole process before unittest's loader ever
builds or runs a `TestSuite`. The absence of any "Ran N tests" line is what
proves it — this invocation form is not "unittest discovered and ran a test,"
it is "importing the file executes it as a script and its exit code escapes
before unittest does anything." Full writeup is now in
`check-control-registration.sh`'s own G2 header comment so the next reader
doesn't have to re-derive it.

### What actually makes 3 of the 4 files reachable

`scripts/check-fact-evidence-replay.sh` — registered in `scripts/check.sh`
(step `facts-replay`) and the justfile — executes every
`proved`/`computed`/`refuted`/`axiom` fact's `checker_command` string
verbatim. **7 `proved` facts** cite three of the four scripts directly by
path (`python3 scripts/tests/check-<name>.py`):

Detail moved to [`../notes/367-control-registration-hyphen.md`](docs/plan/notes/367-control-registration-hyphen.md).

**Status: LANDED (partial, and the partiality is precise). 2026-08-30.**

Eight declarations in a new `crates/axeyum-lean-kernel/src/creal/sup_laws.rs`,
all admitted through `Kernel::add_declaration` with an empty axiom footprint,
every one a first-attempt kernel accept. Decision recorded in
[ADR-0710](docs/research/09-decisions/adr-0710-supon-is-a-supremum-from-below-and-on-a-dense-family-from-above.md).

## What landed

**The approximate least-upper-bound law is complete.**

```
CReal.supOn_approx_lub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) (e : Nat),
  ∃ x, le a x ∧ (le x b ∧ le (supOn F a b hab u) (add (F x) (ofRat (Rat.natDivSucc 1 e))))
```

It must stay approximate: `CReal.evt_attained_max_decides_sign` refutes the
attaining form, which is EVT's row 2. No `argmax`-shaped declaration was added
and none may be.

Supporting it: `CReal.maxRange_attained_approx` (a finite maximum is
approximately attained at one of its samples, by `lt_cotrans`) and
`CReal.supSeq_le_shift`.

**The upper-bound law landed at every sampled point, not at an arbitrary one.**

```
CReal.supSeq_le_supOn             : le (supSeq F a b u k) (supOn F a b hab u)
CReal.supOn_ub_at_supSeq_point    : i ≤ meshLevelCount (supLevel F a b u k)
                                    → le (F (sample i)) (supOn F a b hab u)
CReal.meshMax_le_supOn_add        : le (meshMax F a b (supLevel F a b u k + dd))
                                       (add (supOn F a b hab u)
                                            (ofRat (natDivSucc 1 (meshLevelCount k))))
CReal.supOn_ub_at_fine_mesh_point : i ≤ meshLevelCount (supLevel F a b u k + dd)
                                    → le (F (sample i))
                                         (add (supOn F a b hab u)
                                              (ofRat (natDivSucc 1 (meshLevelCount k))))
```

The last is the strongest: the refinement depth `dd` is free, so the sampled
points can be made as fine as wanted while `k` controls the error
independently.

**The tool the remaining step needs**, `CReal.stepFamily_locate`, is landed —
cell location stated over the ORDER alone, with no mesh algebra in the
induction.

## What does NOT hold

`∀ x, le a x → le x b → le (F x) (supOn F a b hab u)` at an arbitrary `x`.
One declaration; ADR-0710's "What remains, precisely" gives the four-step
route, the level construction, and the reason the locate epsilon cannot be
absorbed by the schedule alone.

## Verdict on the two-axis dominance test

Detail moved to [`../notes/368-supon-laws.md`](docs/plan/notes/368-supon-laws.md).

**Your lane's block (`DONE for this dispatch`, nat-parity-div, 2026-08-30).**
Closed 7 of 10 dispatched mirrors plus flipped 1 pre-existing (see landed-changes).
3 remain open with named blockers below. All work is direct Nat-level kernel
construction (not Int carrier transports — see
`crates/axeyum-lean-kernel/src/nat_prelude/parity_div.rs`'s module doc for why
the `ofNat`/`natAbs` bridge from the `Int` siblings turned out costlier).

Verification run: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 211
passed, 0 failed (was 204 before this lane). `clippy -D warnings` clean on
`-p axeyum-lean-kernel --all-targets --all-features`. `rustfmt --edition 2024
--check` clean. `python3 scripts/validate-facts.py` — 2265 facts, 0 errors.
`python3 scripts/check-mirror-statement-fidelity.py` — verdict=PASS.

**Closed (new kernel theorems, `nat_prelude/parity_div.rs`):**
- `Nat.div_two_mul_two_of_even : Even n -> n/2*2 = n`
  (`F:ml430-nat-div-two-mul-two-of-even-9ccc5340`)
- `Nat.div_two_mul_two_add_one_of_odd : Odd n -> n/2*2+1 = n`
  (`F:ml430-nat-div-two-mul-two-add-one-of-odd-9e3e8b82`)
- `Nat.add_one_lt_of_even : Even n -> Even m -> n<m -> n+1<m`
  (`F:ml430-nat-add-one-lt-of-even-3464b374`)
- `Nat.odd_of_mul_left : Odd (m*n) -> Odd m` (`F:ml430-nat-odd-of-mul-left-2c6c2553`)
- `Nat.odd_of_mul_right : Odd (m*n) -> Odd n` (`F:ml430-nat-odd-of-mul-right-fe6d20ff`)
- `Nat.even_add_one : Even (n+1) <-> !Even n` (`F:ml430-nat-even-add-one-15b5cb18`)
- (private helper) `Nat.even_mul_of_even_left : Even m -> Even (m*n)`, under the
  two `odd_of_mul_*` above.

**Flipped onto a pre-existing theorem, no new proof:**
- `F:ml430-nat-even-iff-024826e9` (`Even n <-> n%2=0`) — matches
  `Nat.even_iff_mod_two_eq_zero`, already in `nat_prelude/parity.rs` before this
  lane started. Flipping it exposed 8 sibling facts (6 `Int` mirrors that already
  used this Nat theorem in their proof terms, `F:ml430-nat-prime-mod-two-eq-one-iff-ne-two-25c35e73`,
  `F:nat-even-xor`) to `check-fact-depends-derived.py`'s dependency graph; fixed
  with `--fix` (their proof terms did not change, only their recorded
  `depends_on`).

**Blocked, named, sized — next lane can pick these up directly:**

Detail moved to [`../notes/369-nat-parity-div.md`](docs/plan/notes/369-nat-parity-div.md).

**Your lane's block (`DONE for 3 of 4, 1 open`, fermat-mirrors, 2026-08-30).**
Closed three of the four dispatched `fermatNumber` mirrors with new,
axiom-free kernel constructions in
`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number_mirrors.rs`:

- `F:ml430-nat-fermatnumber-ne-one-91232d67` (`Nat.fermatNumber_ne_one`) — CLOSED.
- `F:ml430-nat-fermatnumber-mono-b051cee6` (`Nat.fermatNumber_mono`) — CLOSED.
- `F:ml430-nat-coprime-fermatnumber-fermatnumber-161e79c7`
  (`Nat.coprime_fermatNumber_fermatNumber`, Goldbach's coprimality theorem) —
  CLOSED. Route: for `m < n`, `a := 2^(2^m)`, `t := n-m > 0`; `2^(2^n) =
  (a^2)^j` (`j := 2^(t-1)`) via `pow_add` + a locally-built `pow_mul_eq`;
  `modEq (a+1) (a*a) 1` by an EXPLICIT witness (`u=1, v=a`, no subtraction);
  `Nat.mod_eq_pow` + `mod_eq_add_right` give `fermatNumber n ≡ 2 (mod
  fermatNumber m)`; `Nat.ModEq.gcd_eq` + `fermatNumber m` odd
  (`coprime_two_left`) close it. All symbolic (no concrete Fermat number ever
  formed; largest numeral touched is `2`).

All three type-checked by `Kernel::add_declaration` on the FIRST attempt —
no failed intermediate attempts to report. Each is verified: (1) symbolically,
over a genuinely free variable via `infer_in` + `LocalContext` (not just
concrete instantiation — see CLAUDE.md's "concrete instantiation can hide the
bug a symbolic one exposes" entry); (2) at two small concrete pairs
(`fermatNumber 0/1 = 3/5`, `1/2 = 5/17`, the second exercising the theorem's
other case branch and its `coprime_symmetric` swap); (3) against a REFLEXIVE
NEGATIVE CONTROL for the coprime theorem confirming its `Ne m n` hypothesis
is load-bearing: `gcd(fermatNumber 0, fermatNumber 0) = gcd(3,3) = 3`,
explicitly asserted NOT defeq to `1`.

New test: `nat_prelude_tests.rs::
fermat_number_mirrors_apply_at_free_and_concrete_instances_with_a_reflexive_negative_control`.
`cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 208 passed (was 204
before this lane), 0 failed. `cargo clippy -p axeyum-lean-kernel --all-targets
--all-features -- -D warnings` — clean. `cargo fmt --all --check` — clean.

Detail moved to [`../notes/370-fermat-mirrors.md`](docs/plan/notes/370-fermat-mirrors.md).

**Your lane's block (`WIP`, pow-add-prime, 2026-08-30).**

`F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (`Nat.Prime (a^n+1) -> exists m, n
= 2^m`, the classical fact behind Fermat primes) stays `open`. The classical
proof needs an alternating-sum cofactor (`x^d+1 = (x+1)*(x^{d-1}-x^{d-2}+...+1)`
for odd `d`), and this kernel has no signed sum over ℕ — so rather than build
one (pairing terms, or transporting through `Int`), I sidestepped it entirely.

**What landed** (`crates/axeyum-lean-kernel/src/nat_prelude/pow_add_prime.rs`,
new file, wired into `nat_prelude.rs` as the last `declare_*` call):

- `Nat.pow_mul : forall a e k, pow a (mul e k) = pow (pow a e) k` — mirrors
  `Int.pow_mul`'s proof shape (`int_prelude/algebra.rs`).
- `Nat.dvd_pow_add_one_of_odd_exp : forall x t, dvd (add x 1) (add (pow x (succ
  (mul 2 t))) 1)` — `x+1 | x^{2t+1}+1` for every `x`, by an OUTER case split on
  `x` (0 is trivial: `dvd 1 _`) then an INNER induction on `t` for `x = succ
  xp`, using only `dvd_add`/`dvd_mul_left` plus one subtraction-free identity
  `x^2 = x'*(x+1)+1` (`x'` is the genuinely free predecessor standing in for
  `x-1`, so `Nat.sub` never appears).
- `Nat.dvd_pow_add_one_of_odd_mul_exp : forall a e t, dvd (add (pow a e) 1)
  (add (pow a (mul e (succ (mul 2 t)))) 1)` — `a^e+1 | a^{e*(2t+1)}+1`, the
  reusable "odd-factor divisibility" step named in the fact's own brief as a
  good outcome on its own (`d := 2t+1`; combines `pow_mul` with the lemma
  above at `x := a^e`).

All three are genuinely axiom-free theorems (checked via
`Kernel::axiom_footprint`), admitted on the FIRST attempt against a real
kernel (no debugging round-trips needed once the algebra chains were worked
out on paper first). Verified both at a free `(a,e,t)` (the theorem's own
`forall` IS the free-variable check, plus one `infer_in` application at fresh
fvars) and at the concrete discriminating instance `a=2, e=1, t=1`: `3 | 9`
(`2^3+1=9=3*3`, exactly the smallest instance the classical argument would
use to show a prime `a^n+1` cannot have an odd exponent factor). Largest
numeral formed anywhere in the proofs or tests: `9` (`2^3+1`) — everything
else is symbolic, since this is a proof about free variables, not a
computation.

Detail moved to [`../notes/371-pow-add-prime.md`](docs/plan/notes/371-pow-add-prime.md).

Status: **COMPLETE** (2026-08-30) — design/measurement lane, no kernel
declarations built, no fact edited.

Extended ADR-0603's graded-statement-family treatment from the four Spivak
real-analysis families (MVT, LUB, Taylor remainder, FTA) to **number theory**
(Stein, Shoup) and **linear algebra** (Boyd–Vandenberghe), the curriculum's two
untreated destinations.

## The central finding

`Nat.le_total`, `Int.le_total`, `Rat.le_total` and `Rat.le_or_lt` are **proved,
axiom-free theorems**, while `CReal.le_total`/`lt_total` are absent (controls:
`CReal.lt_cotrans`, `CReal.apart_cotrans`, FOUND). So the decision principle
that every real-analysis row 2 extracts is *already in the environment* for
ℕ/ℤ/ℚ, and no number-theoretic or rational-linear-algebra statement can have a
row 2 of that kind. That is a positive measurement of emptiness, not a failure
to find one — the distinction ADR-0603 Amendment 4 exists to protect.

Two boundaries survive, and one is **stronger** than anything analysis
produces: the unrestricted least-number principle reduces to *full* excluded
middle (analysis's row 2s reach only LLPO). The other is not a decision
boundary at all but an expressiveness one, and gets its own row.

## Landed

| Change | Path |
|---|---|
| The measurement note: families, rows, targets, both subjects | `docs/curriculum/graded-statement-families-number-theory-and-linear-algebra.md` |
| ADR: row 2 of a decidable subject; introduces **row 2′** | `docs/research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md` |
| Corrected — 3 of 4 "Lean-horizon" theorems are landed | `docs/curriculum/03-destinations/number-theory.md` |
| Corrected — the kernel layer was missing entirely | `docs/curriculum/03-destinations/linear-algebra.md` |
| Lens note: the ✅/◐/✗ tags measure row 3 only | `docs/curriculum/foundational-books/source-tocs.md` |
| Comparison table now separates scenario from kernel layer | `docs/curriculum/DEPTH.md` |

`curriculum.toml` was deliberately **not** touched — see "left open" below.

## Verdicts

Detail moved to [`../notes/372-graded-families-beyond-analysis.md`](docs/plan/notes/372-graded-families-beyond-analysis.md).

**Library programme (`DONE`, library-construction-roadmaps, 2026-08-30).**
ADR-0717 and four detailed roadmaps now define the new L0–L4 focus: universal
theorem credit; pinned declaration-graph authority; graph join and
infrastructure ranking; declarative, counterexample-first discovery; and a thin
Lean adapter before demand-gated source compatibility. Project-wide plan
sources, the plan index, research roadmap, and generated root plan carry the
same order. Implementation belongs to new disjoint graph-authority,
graph-ranking, safety-contract, and discovery lanes; this planning lane owns no
producer, fact status, or generated graph artifact.

## Status

**DONE.** ADR-0603 row 2 for the least-number principle over the naturals is
landed, kernel-checked, axiom-free, and registered in the fact ledger with its
converse. This is the first row-2 result in the repository that is not about the
reals, and it is strictly stronger than the two that are.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/least_number.rs` — five theorems, all
admitted by `Kernel::add_declaration` on the first attempt, all with an empty
`axiom_footprint`. Rendered types read from
`nat_theorem_inventory` (`--release`), one name per invocation:

```text
Nat.lnp_unrestricted_implies_em :
  (∀ (Q : AxNat → Prop),
     (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k)))
  → ∀ (P : Prop), Or P (Not P)

Nat.em_implies_lnp :
  (∀ (P : Prop), Or P (Not P))
  → ∀ (Q : AxNat → Prop),
      (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k))

Nat.lnp_of_pointwise_decision :
  ∀ (Q : AxNat → Prop), (∀ n, Or (Q n) (Not (Q n)))
  → (∃ n, Q n) → ∃ m, And (Q m) (∀ k, AxNat.lt k m → Not (Q k))

Nat.lnp_bounded_search :
  ∀ (Q : AxNat → Prop), (∀ n, Or (Q n) (Not (Q n))) → ∀ n,
    Or (∀ k, AxNat.lt k n → Not (Q k))
       (∃ m, And (AxNat.lt m n) (And (Q m) (∀ k, AxNat.lt k m → Not (Q k))))

Nat.lnp_decidable :
  ∀ (dec : AxNat → Bool) (n : AxNat), Eq Bool (dec n) Bool.true
  → ∃ m, And (Eq Bool (dec m) Bool.true)
             (∀ k, AxNat.lt k m → Eq Bool (dec k) Bool.false)
```

Facts: `F:nat-lnp-unrestricted-implies-em` (row 2) and `F:nat-lnp-decidable`
(the decidable-fragment exact form). ADR-0725 records the two design decisions
ADR-0716 did not make.

## The three things a reviewer should check first

Detail moved to [`../notes/373-lnp-implies-em.md`](docs/plan/notes/373-lnp-implies-em.md).

Status: PARTIAL — the largest verified piece landed, precise handoff below.
The full theorem is NOT closed.

## The ask

Prove `a^phi(n) = 1 (mod n)` for `gcd(a, n) = 1`. ADR-0716 named it the
second-highest-yield remaining number-theory target on the grounds that
"both residue-permutation ingredients are already landed":
`Int.euler_unit_coprime` and `Int.euler_unit_injective`.

## ADR-0716's claim, verified against the kernel and the tree

Both named theorems exist, are correctly stated, and are axiom-free
(confirmed via `theorem_dependency_inventory` and `nat_axiom_inventory
--require-axiom-free integer`, both re-run for this lane's own additions
below). **But that is not the same as the theorem being within reach**, and
the file that landed them says so in its own module doc, in detail, which
ADR-0716 did not carry forward:

`int_prelude/euler_totient.rs`'s own doc records that Euler's theorem does
NOT land there, because two things are missing:

1. A product over a **predicate-defined subset** of `[0,n)` (Euler's proof
   folds a product over `{k < n : gcd(k,n)=1}`, not the full range).
2. A proof that such a restricted product is invariant under a
   predicate-preserving permutation.

At the time that file was written, neither existed anywhere in the kernel.
Since then, `nat_prelude/subset_product.rs` landed `Nat.prodRangeIf`
(definition + defining equations + `congr_lt`) — but **that file's own doc
says permutation invariance is STILL missing**, and sizes porting the
missing induction (an adjacent-transposition swap, the mechanism
`Int.prodRange_swap`/`Int.prodRange_permute` use in `prod.rs`) at roughly
650 lines, "same order of magnitude" as the whole file — because **no such
lemma exists for `Nat.prodRange` at all**, only for `Int.prodRange`.

So the honest state before this lane: the two named ingredients are real,
but they are inputs to a step (subset-product permutation invariance) that
had not been built in EITHER prelude, for two different reasons (Nat: no
predicate-restricted product API at all, until subset_product.rs; Int: the
API exists via a different route but the swap induction was never ported
there either). One lane closed a target with zero new lemmas against a
two-or-three-lemma estimate this session; this is not that case — real
work remained, and it is a good deal more than "wire it up".

## Carrier decision: ℤ, not ℕ — and why

Detail moved to [`../notes/374-euler-theorem.md`](docs/plan/notes/374-euler-theorem.md).

**Status: LANDED.** `CReal.supOn_ub` is admitted, axiom-free, first-attempt
kernel accept. ADR-0733.

```
CReal.supOn_ub : ∀ F a b (hab : le a b) (u : UniformlyContinuousOn F a b) (x : CReal),
  le a x → le x b → le (F x) (supOn F a b hab u)
```

This is the one declaration ADR-0710 named as remaining between `CReal.supOn`
and comparability with Mathlib's `IsCompact.exists_isMaxOn`. With
`CReal.supOn_approx_lub` it is the pair that characterizes `supOn` as a
supremum: an upper bound at every point of `[a, b]`, and approached to any
requested accuracy at an exhibited point.

## Measured

| check | result |
| --- | --- |
| `creal_prelude_builds` before | **110.54 s** |
| `creal_prelude_builds` after | **110.00 s** (flat) |
| `cargo test -p axeyum-lean-kernel --lib creal::` | **201 passed, 0 failed** |
| `every_creal_declaration_is_checked_and_axiom_free` | passes — reads `kernel.environment()`, so `CReal.supOn_ub` is a `Theorem` with an empty axiom footprint |
| `cargo fmt --all --check`, clippy `-D warnings` on this crate | clean |

The flat prelude build matters: none of the defeq traps this development has
accumulated (a `Definition` forced to unfold, a concrete witness driving
partial evaluation) was tripped.

## ADR-0710's four steps: three held, one drifted CHEAPER

The route in ADR-0710 was accurate and was followed. The one drift is in our
favour:

- **Step 2** predicted the refinement depth `dd` would come from `Nat.le_dest`,
  "an `Exists` into a `Prop`, which is permitted". It does not have to.
  Choosing `j := supLevel F a b u kk + (Nat.size c + Nat.size outer2)` makes
  `dd` **concrete**, so the obligation reduces to
  `Nat.le dd (Nat.add level dd)` and **no existential is eliminated anywhere in
  the proof**. One summand satisfies both consumers at once.
- Steps 1, 3 and 4 held verbatim, including the arithmetic in step 3.
- Step 1's three interface identities were exactly what was needed and no more.
  Two are re-derivations of `creal/supremum.rs` private helpers
  (`sample_zero_equiv`, `sample_succ_equiv`); `mesh_endpoint_equiv`
  (`P N + Δ ~ b`) is new. Worth knowing:
  `creal/monotone.rs`'s `subdivisionPoint_in_bounds` already runs those same
  three steps but lands a `le` rather than an `Equiv`, so it could not be
  reused — only the shape could.

## Where the margin came from, since `supLevel` has none

`supLevel`'s schedule is exactly fine enough for the modulus at the
corresponding accuracy, which is why an off-mesh point cannot reuse it. The
margin is bought in **two independent places, neither of which is a scheduled
level**, and they are not interchangeable:

Detail moved to [`../notes/375-supon-ub-arbitrary.md`](docs/plan/notes/375-supon-ub-arbitrary.md).

**Your lane's block (`DONE for this dispatch`, parity-finish, 2026-08-30).**
All three facts handed off by `nat-parity-div` (see
`docs/plan/status/369-nat-parity-div.md`) are closed. All three sizings from
the handoff were WRONG in the optimistic direction (the two "no missing
lemma, just a doubled case split" facts needed real new infrastructure; the
one sized as "more substantial... needs a new arithmetic identity" turned out
to need none) — see below for what each cost.

Verification run: `cargo test -p axeyum-lean-kernel --lib nat_prelude::` —
221 passed, 0 failed (was 218 before this lane's first commit; +3 net over
the two new files plus one shared test/coverage-list registration per
declaration). `clippy -D warnings` clean on `-p axeyum-lean-kernel
--all-targets --all-features`. `rustfmt --edition 2024 --check` clean on
every touched file. `python3 scripts/validate-facts.py` — 2270 facts, 0
errors. `python3 scripts/check-mirror-statement-fidelity.py` —
verdict=PASS. `python3 scripts/check-autogenesis-holdout-isolation.py` —
settled=0, references=0, verdict=PASS.

**Closed:**

Detail moved to [`../notes/376-parity-finish.md`](docs/plan/notes/376-parity-finish.md).

**Your lane's block (`DONE for this dispatch`, fermat-easy, 2026-08-30).**
All five dispatched facts closed, axiom-free, in one new dispatcher
(`declare_fermat_number_easy_all`) appended to
`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number_mirrors.rs`:

- `F:ml430-nat-fermatnumber-zero-ca7aac67` — `Nat.fermatNumber 0 = 3`
- `F:ml430-nat-fermatnumber-one-b1b0798f` — `Nat.fermatNumber 1 = 5`
- `F:ml430-nat-fermatnumber-two-3aa3bfc4` — `Nat.fermatNumber 2 = 17`
- `F:ml430-nat-odd-fermatnumber-251041a5` — `∀ n, Odd n.fermatNumber`
- `F:ml430-nat-fermatnumber-strictmono-acbcb8c6` — `StrictMono Nat.fermatNumber`

As ADR-0695 predicted, the three closed equations were pure `refl` once
stated — `fermat_number_evaluates_correctly` already asserted them by
`def_eq`, so declaring them as their own `Theorem`s (rather than test
assertions) was the entire task. **Largest formed numeral anywhere in this
lane: 17** (`fermatNumber 2 = 17`, the ceiling the brief set — `n = 3` would
form 257). The two general theorems (`odd_fermatNumber`,
`fermatNumber_strictMono`) are fully symbolic; their largest formed numeral
is the base `2`.

**`odd_fermatNumber`** reused the file's own private
`odd_fermat_number_local`/`even_pow_two_of_pos` helpers verbatim (already
built for `coprime_fermatNumber_fermatNumber`'s proof) — no new proof
machinery, just a new `d.theorem` wrapper stating it as its own declaration.

**`fermatNumber_strictMono`** did NOT go through `fermatNumber_mono` plus a
strict step (the brief's suggested route) — building directly with
`pow_lt_pow_of_lt` climbed twice turned out to be no harder than the
`Monotone` proof's `Le`-branch, since the `Lt` hypothesis needs no
`lt_or_eq_of_le` case split at all. The one new piece is
`add_lt_add_right_local` (`Lt a b → Lt (add a c) (add b c)`, via `add_comm` +
`add_lt_add_left`, since only the `Le`-strength `add_le_add_right` exists
directly in this prelude) — ~15 lines, transport-based, reusable by any
future `Lt`-shaped `+c` step.

**No blockers.** All five closed on the first construction attempt; no
handoff needed for a next lane.

Detail moved to [`../notes/377-fermat-easy.md`](docs/plan/notes/377-fermat-easy.md).

**Your lane's block (`DONE`, pow-add-prime-finish, 2026-08-30).**

`F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (`Nat.Prime (a^n+1) -> exists m,
n = 2^m`, the classical fact behind Fermat primes) is now `proved`, axiom-free,
`proof_route: kernel-lean`.

**The prior handoff's sizing of the remaining work did NOT hold up, and it is
worth recording why.** It called the odd-factor extraction ("`n` not a power
of two has an odd factor `> 1`") "a genuine well-founded-recursion
undertaking" needing `WellFounded.fix`, on the grounds that every existing
strong-induction construction in this prelude (`gcd`, `bezout_witnesses`,
`modeq`, `wilson`, `exists_prime_factorization`) uses it. That generalization
was wrong: **ordinary structural `Nat.rec` on a FUEL BOUND** (`Le n fuel`,
instantiated at `fuel := n` via `le_refl`) gives the induction hypothesis for
*every* `n' <= fuel-1`, which is exactly the strong-induction shape this
argument needs (recurse on `half := div n 2`, not on `n`'s predecessor). No
`WellFounded`, no `Acc`, no `lt_well_founded` anywhere in the final
construction. `bit_order.rs`'s `msb_exists_of_le_fuel` already uses this exact
pattern for an unrelated predicate (most-significant-bit existence) and was
the template that made the three-lemma bound (`lt_two_mul_of_pos` +
`lt_of_lt_of_le` + `le_of_succ_le_succ`) cheap to find.

**What landed** (`crates/axeyum-lean-kernel/src/nat_prelude/pow_add_prime.rs`,
extended — same file the prior lane started, ~600 new lines):

Detail moved to [`../notes/378-pow-add-prime-finish.md`](docs/plan/notes/378-pow-add-prime-finish.md).

**DONE (`totient-gcd-mul`, 2026-08-30).** Closes
`F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7` (the last of the three
`ml430` totient mirrors ADR-0668 opened), the largest of the three:

```text
Nat.totient_gcd_mul_totient_mul : ∀ a b,
  totient(gcd a b) * totient(a*b) = totient(a) * totient(b) * gcd(a,b)
```

New file `crates/axeyum-lean-kernel/src/nat_prelude/totient_gcd_mul.rs`, one
`declare_totient_gcd_mul_all(&mut d, &p)?` call wired in after
`declare_totient_dvd_chain_all`. `nat_prelude::` 221 → 222 passed, 0 failed.
`cargo fmt --all --check`-equivalent (`rustfmt --edition 2024` on the touched
files) clean; `cargo clippy -p axeyum-lean-kernel --all-targets -- -D
warnings` clean; `python3 scripts/validate-facts.py`: 2270 facts, 0 errors;
`python3 scripts/check-fact-depends-derived.py --fix`: nothing to fix.

## ADR-0668's sizing: held on two counts, corrected on one

ADR-0668 called this target "the largest of the three; strong induction on
`gcd(a,b)`, base case the already-landed multiplicativity, reducing to a
four-leaf ε truth table where Euclid's lemma is load-bearing (fails at 450
composite triples)."

Detail moved to [`../notes/379-totient-gcd-mul.md`](docs/plan/notes/379-totient-gcd-mul.md).

**Lane:** `nt-certificates`
**Status:** landed — ADR-0745
**Date:** 2026-08-30

## What this lane was for

ADR-0716 measured that ADR-0603's **row 2** (the boundary refutation) is
provably empty for ℕ, ℤ and ℚ, so number-theoretic dominance has to come from
rows 1 + 3: a statement, an executable, and a re-derivable certificate. It then
measured the row-3 obligation as unmet.

## The gap, re-measured rather than inherited

Positive controls in the same command, GNU `grep` (not the interactive
`ugrep`):

| file | `verify_`/`check_` fns | plain `fn`s |
| --- | --- | --- |
| `crates/axeyum-cas/src/ntheory.rs` | **0** | 39 |
| `crates/axeyum-cas/src/ntheory_advanced.rs` | **0** | 29 |
| `crates/axeyum-cas/src/taylor.rs` (control) | 8 | — |
| `crates/axeyum-cas/src/mvt.rs` (control) | 9 | — |

Confirmed: 68 number-theoretic functions, zero verifiers, in a crate whose
analysis modules carry 8–9 apiece.

## What landed

`crates/axeyum-cas/src/ntheory_certify.rs` — four certificate types, four
independent checkers, self-checking producers. Modular arithmetic is the
module's own so a shared `mod_pow` defect cannot fool both sides; agreement
with `ntheory::mod_pow` is tested at 150 points including modulus `i128::MAX`.

- `PrattCertificate` / `check_primality_certificate` — recursive Lucas.
- `CompositeCertificate` / `check_composite_certificate` — a divisor. Kept a
  **separate type**; the two directions are never interchangeable.
- `FactorizationCertificate` / `check_factorization_certificate` — factor list
  + per-base Pratt + product identity + strict ascending order.
- `CrtCertificate` / `check_crt_certificate` — `Solution` with a **least**
  common multiple, or a named `Inconsistent` pair.

33 adversarial fixtures, 0 failures. Plus the 40 pre-existing `ntheory` tests:
73 passing under `--lib ntheory`.

## Trust anchor

**Nothing reconstructs through `Kernel::add_declaration`, deliberately**, and
the module doc labels itself `cas-internal` (ADR-0601). Over unary numerals a
reconstruction of `n = d · e` would be an `Eq.refl` on a numeral tower —
exactly the `refl`-shaped, substance-free reconstruction
`scripts/check-cas-substance.py` exists to catch.

## Guard-kill measurement

`scripts/tests/test-ntheory-certificate-guards.sh`:
`measured=23 survivors=3 not_measured=0`, exit 0.

Twenty verdict-bearing guards each killed (sixteen by one test, four by two).
Three survivors — G1, G5, G10 — **found by the sweep, not predicted**, each
provably unable to change a verdict, each documented at its site and pinned in
`EXPECTED_SURVIVORS` with a two-way assertion.

Detail moved to [`../notes/380-nt-certificates.md`](docs/plan/notes/380-nt-certificates.md).

**Your lane's block (`DONE`, rat-matrix-layer, 2026-08-30).** See the detail below.

**Track:** Mathematics 2026-08 — linear algebra, the general-dimension layer
**Phase:** ADR-0761 landed; product, associativity, bilinearity, identity and
both unit laws in the kernel, axiom-free
**Date:** 2026-08-30

## Summary

`Rat.dotN` gave this kernel an inner product at arbitrary dimension over ℚ,
Cauchy–Schwarz included. One index up there was nothing: every determinant
declaration was fixed-size with entries passed as separate scalar arguments,
and `F-determinant-multiplicative-over-constructed-rationals` states
`det(AB) = det A · det B` by writing out all eight entries.

This lane built the matrix layer on the encoding `sumRange` and `dotN` already
sit on. A matrix is a function `Nat -> Nat -> Rat` with dimensions as ordinary
arguments; `Rat.matMul A B k` is itself such a function, so
`matMul (matMul A B k) C m` is well-typed with no coercion.

## Delivered

`crates/axeyum-lean-kernel/src/rat_prelude/matrix_n.rs` — thirteen
declarations, all axiom-free:

| declaration | statement |
|---|---|
| `Rat.matMul` | `A B k i j := sumRange (fun t => A i t * B t j) k` |
| `Rat.matMul_zero` | `matMul A B 0 i j = 0` (`Eq.refl`) |
| `Rat.matMul_succ` | `matMul A B (succ k) i j = matMul A B k i j + A i k * B k j` (`Eq.refl`) |
| `Rat.matMul_assoc` | `matMul (matMul A B k) C m i j = matMul A (matMul B C m) k i j` |
| `Rat.matMul_add_left` | `matMul (fun r t => A1 r t + A2 r t) B k i j = matMul A1 B k i j + matMul A2 B k i j` |
| `Rat.matMul_add_right` | the mirror, via `left_distrib` |
| `Rat.matMul_smul_left` | `matMul (fun r t => c * A r t) B k i j = c * matMul A B k i j` |
| `Rat.sumRange_delta` | `(∀ t, t ≠ i → f t = 0) → Lt i n → sumRange f n = f i` |
| `Rat.matId` | `i j := if Nat.beq i j then 1 else 0` |
| `Rat.matId_diag` | `matId i i = 1` |
| `Rat.matId_off_diag` | `¬(i = j) → matId i j = 0` |
| `Rat.matMul_id_left` | `Lt i n → matMul matId A n i j = A i j` |
| `Rat.matMul_id_right` | `Lt j n → matMul A matId n i j = A i j` |

Every statement is **pointwise** (`… i j = … i j`), and that is forced:
`funext` is absent from this kernel (control of the same kind, present:
`congrFun'`), so an `Eq` between two `Nat -> Nat -> Rat` values is not
available. Pinned by `the_matrix_associativity_statement_is_pointwise`, which
asserts the rendered type verbatim.

Also:

Detail moved to [`../notes/381-rat-matrix-layer.md`](docs/plan/notes/381-rat-matrix-layer.md).

Lane: `l0-safety-matrix`
Phase: ADR-0717 L0, roadmap phase **S0** — complete.
Decision: [ADR-0746](docs/research/09-decisions/adr-0746-the-safety-matrix-is-generated-and-gated.md)

## Status

S0's exit criterion is met and gated. `scripts/gen-safety-matrix.py` generates
`artifacts/safety-matrix/safety-matrix.tsv` (one row per proved fact, exactly
once) and `safety-matrix-summary.md`; `--check` runs in both `scripts/check.sh`
and the justfile, and `check-aggregate-scope.sh` still reports its recorded 64
divergences, so the registration is two-sided.

Six mutations, three distinct guards, each firing through the right one —
deleting a controlled fact, dropping its checker, unsettling it, deleting an
**uncontrolled** fact, downgrading an own-subject checker to the shared prelude
sweep, and breaking a classifier so it matches nothing. Full table in ADR-0746.

**No fact was edited.** This lane is measurement only.

## The numbers a later phase should start from

2,270 facts, 2,117 `proved`. Median protections per fact: 3.

| protection | facts / 2117 |
|---|---:|
| `env_footprint` (prelude-wide sweep) | 1859 |
| `kernel_theorem` (explicit binding) | 1466 |
| `coverage_bearing_checker` (own subject) | 1442 |
| `exact_statement` (drift pin) | 142 |
| `semantic_falsification` | 91 |
| `per_theorem_footprint` | 59 |
| `circularity` | 38 |
| `mutation_control` | 14 |
| `independent_replay` | 8 |

53 facts hold none of the nine. 523 hold one, and for 400 of those the one is
the prelude sweep.

Checker fan-out: 2,284 distinct commands, **largest 463**
(`--require-axiom-free creal`), then 318 and 280. 2,221 commands serve exactly
one fact; only 48 proved facts have no checker of their own and 17 cite none.

## Three findings that should change how a later phase is scoped

1. **The evidence `kind` enum no longer discriminates.** 1,901 rows declare
   `exhaustive-enumeration` or `instance-pin` while their `supports` records an
   axiom footprint. Reading `kind` at face value turns a true semantic-
   falsification count of 91 into 1,992. S3 must not size itself off `kind`.

2. **The statement-drift gate covers 6.8% of settled facts and exits 0.**
   `check-settled-fact-statements.py` reports `settled=2119|pinned=144`; a fact
   absent from the manifest is treated as newly settled, never as a gap. S1's
   first move is a coverage assertion on that manifest, not new machinery.

Detail moved to [`../notes/382-l0-safety-matrix.md`](docs/plan/notes/382-l0-safety-matrix.md).

**Status: DONE — draw 8 is DECLINED, for a reason draw 7's handoff could not
have measured.**
[`check-dispatchable-frontier.py`](scripts/check-dispatchable-frontier.py)
stays RED at **1 dispatchable against a floor of 10**, and no refill can clear
it until **two** constructions land.

Decision record:
[ADR-0762](docs/research/09-decisions/adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md).
Measurements and reproducible probes:
[`../notes/383-nursery-draw-8.md`](docs/plan/notes/383-nursery-draw-8.md).

Nothing was written. `FAMILY_MODULES`, `FAMILY_ROUTES`, both manifests, the
statable vocabulary, the environment snapshot and the headroom file are
byte-identical to the merge-base; no row moved partition; no attestation count
was raised; no held-out row was touched.

## Draw 7's prediction: half right, and wrong by a whole constant

**Right.** The un-owned floor is down to seven modules — exactly the four draw 7
took, removed — and **not one is held-out-safe**. Each is adjacent to a
published development or train family, or R9-contaminated, or both. Dist is
unchanged at 2/10. Re-derived, not inherited.

**Wrong.** "One more constant" opens nothing. Enumerating all subsets of size
4, 5 and 6 with R5's two-family minimum and every cycle position ≡ 0 mod 3
required to be held-out-safe:

    no new constant                     LAWFUL family sets: 0
    with ONLY Nat.nthRoot declared      LAWFUL family sets: 0
    with ONLY NatCast.natCast declared  LAWFUL family sets: 0
    with Nat.nthRoot AND Squarefree     LAWFUL family sets: 10

Draw 7 could spend one constant because `Mathlib.Data.Nat.Nth` was banked and
clean. It spent Nth too, so the held-out-safe set is **empty rather than one
short**, and R5 is hard-coded at two.

## Both screens, for every candidate

| candidate constant | opens | pool | screen 1 (R9, exact name) | screen 2 (namespace sweep) | closed-eval spent | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `Nat.nthRoot` | `…Pow.NthRootLemmas` | 13 | **0/10** | **0** declarations | 0 | **clean — the one candidate** |
| `Squarefree` | `Mathlib.Data.Nat.Squarefree` | 11 | **0/10** | **0** declarations | 0 | judged unsafe on adjacency |
| `NatCast.natCast` | `Init.Data.Int.OfNat` | 14 | 0/10 | 0 | 0 | **rejected — omega vocabulary** |
| `Nat.centralBinom` | `…Choose.Central` | 14 | 0/10 | — | **1** | not safe — natural-binomial development |
| `Nat.div2` / `Nat.bodd` | `Mathlib.Data.Nat.Bits` | 14 / 12 | 0/10 | — | 0 | not safe — natural-bitwise development |

Detail moved to [`../notes/383-nursery-draw-8.md`](docs/plan/notes/383-nursery-draw-8.md).

Lane: `l0-s1-statement-identity`
Phase: S1 of the trusted-library safety roadmap (ADR-0717, selected by ADR-0746)
Decision: [ADR-0763](docs/research/09-decisions/adr-0763-statement-identity-is-pinned-for-every-settled-fact-and-absence-is-a-violation.md)
Status: **COMPLETE.** S1's exit criterion holds and is executed on every merge.

## The gap S0 measured, re-measured from the ledger

`artifacts/safety-matrix/safety-matrix.tsv` reported `exact_statement`
142 / 2117 — the thinnest column. Split by population, read from the facts
directly so the two measurements are independent:

| population | settled | pinned before | pinned after |
|---|---:|---:|---:|
| all settled facts | 2120 | 144 | **2120** |
| `F:ml430-*` mirrors | 375 | 27 | 375 |
| native (non-mirror) | 1745 | 117 | 1745 |

Mirrors already had a stronger guard — `check-mirror-statement-fidelity.py`
hashes `formal.statement` against a preregistered catalog, 502 of 514 verified.
**The native 1,745 were the real gap**, and they are the half of S1's
specification that had nothing behind it.

### The old gate could not fail on absence, and that is measured

`check-settled-fact-statements.py` had `if pin is None: continue` — absence read
as "newly settled", never as a gap. Loading `HEAD~2`'s checker with `HEAD~2`'s
144-pin manifest against the live facts:

```
clean                                        -> exit 0
SWAPPED BINDERS on F:creal-ivt-approx        -> exit 0   ACCEPTED
same mutation on a fact it DID pin (control) -> exit 1   rejected
```

The control is what makes this a finding rather than a bug report: the gate
worked correctly and simply had no opinion about 1,976 facts.

## What landed

**Statement identity for every settled fact.** Manifest schema 2 pins, per
fact, the kernel rendering (`formal.statement`), the reader-facing prose
(top-level `statement`), and the declaration it names (`formal.kernel_theorem`),
with superseded digests preserved in `history`. Pinning the prose is new: a
native fact makes two claims, and the field most readers see was unwatched.

**Absence is a violation, and the ratchet cannot be loosened.**
`coverage_floor` bounds unpinned facts (0), identity bindings (1,294) and
headerless statements (30) — and **slack is itself a violation**. Raising an
allowance to sneak something past makes the next run fail because the actual
count is then below the raised allowance. Loosening is self-reverting rather
than merely discouraged.

**`--write` can no longer launder drift.** It used to rebuild the pins from
current state unconditionally, so running it after a drift re-pinned the damage
and the gate went green.

Detail moved to [`../notes/384-l0-s1-statement-identity.md`](docs/plan/notes/384-l0-s1-statement-identity.md).

Lane: `l0-s3-semantic-controls`
Phase: ADR-0717 L0, roadmap phase **S3** — complete.
Decision: [ADR-0752](docs/research/09-decisions/adr-0752-semantic-controls-are-a-retained-fixture-pack-not-a-review-step.md)

## Status

S3's exit is met and gated. `scripts/check-semantic-control-fixtures.py`
executes the retained fixture pack in
`scripts/semantic_control_fixtures.py`, pins its shape in
`artifacts/semantic-controls/fixture-pack.json`, and is registered in **both**
`scripts/check.sh` and the justfile.

    fixtures=13|executed=9742|mutations=19|killed=18|also_true=1|survived=0
    load_bearing=8|semantic_falsification=91|proved=2117
    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|
      settled=0|references=0|verdict=PASS

**No fact was edited.** Not `epistemic_status`, not `proof_route`, not
`axiom_footprint`, not `formal.statement`.

## The pack

13 fixtures, each a real defect this session produced and caught, or the valid
control one line away from it: the coprimality-independence claim false at
26/26 non-coprime pairs; the composite totient control vacuous by mathematics;
the least-number-principle control that passed on a sort mismatch; the Pratt
certificate for 91 that only completeness rejects; the CRT certificate (9, 24)
that only leastness rejects; the NRA bound recording a constant but not
strictness, over a satisfiable query.

Three classes. `false` must be refuted. `vacuous` must produce **zero**
discriminating instances — the fixture asserts the zero, not its own
greenness. `valid` must be accepted, must discriminate, and must kill at least
one mutation. **Zero executed cases is failure** per fixture, for the pack, and
for an empty pack.

An unfalsified mutation declared `also_true` is classified for review, never
failed. One such: `eq-to-le` on the totient identity, where the weakened
statement is true.

## The honest count

**8 of 2,117** proved facts have a control this gate demonstrated would fail if
the property failed. 91 is the upper bound — S0's `semantic_falsification`
column, which counts facts carrying a semantic evidence row whether or not it
discriminates. 1,992 is what `kind` would give, and the census never reads
`kind`: it reads S0's generated column, which classifies from `supports`.

The 84-fact difference between 91 and 8 is **not** 84 vacuous controls. It is
84 controls not demonstrated either way, and the summary keeps those apart.

## Mutation kill sets

21 mutations through `scripts/tests/mutation_controls.py
semantic-control-fixtures`, against 28 controls. **Every one `killed 1`,
naming a distinct test. No survivors, nothing unmeasured.**

## Three defects found in the tools, not the subject

Detail moved to [`../notes/385-l0-s3-semantic-controls.md`](docs/plan/notes/385-l0-s3-semantic-controls.md).

Lane: `l0-s4-independent-replay`. Phase S4 of the trusted-library safety
roadmap (ADR-0717). Decision: [ADR-0760](docs/research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md).

## Status

S4's grading discipline is landed and gating. The census executes rather than
reading claims, `missing=0` is enforced, the inheritance guard is attested by
Lean itself, and both mutation classes are rejected. Two findings came out of
it, one of which says a shipped fact claims replay it does not have.

## The measurement

One run, pinned Lean 4.30.0 (`d024af09`), whole `creal` carrier,
`cargo test -p axeyum-lean-kernel --test real_lean_replay_census`:

    population=2045 representable=1972
      theorem_type_not_prop=48 blocked_by_dependency=25
    checked=1972 expected=1972 missing=0 extra=0
    5 passed; 0 failed; finished in 240.80s

Flagship grades, each read out of the run:

| subject | Axeyum | pinned Lean |
|---|---|---|
| `CReal.ivt_approx` | accepted | **replayed** |
| `CReal.ivt_exact_root_decides_sign` | accepted | **replayed** |
| `CReal.evt_attained_max_decides_sign` | accepted | **replayed** |
| `CReal.fermat_interiorExtremum` | accepted | **replayed** |
| `CReal.rolle_interiorExtremum` | accepted | not representable — blocked by `CReal.hasDerivative_neg` |
| `CReal.mvt_interiorExtremum` | accepted | not representable — blocked by `CReal.hasDerivative_add` |

## Findings

**1. This kernel admits `Theorem`s whose type is not a proposition; Lean's
kernel refuses them.** 48 declarations, plus 25 blocked by depending on one.
`CReal.weierstrassMTest` concludes in `CReal.UniformConvergesOn`, which
`creal/uniform_convergence.rs` deliberately makes `Type`-valued so the
convergence rate is data. The declarations are intentional and the reason is
sound; what was missing is that nothing recorded them as outside what Lean will
accept **as a theorem**. Not a demonstrated soundness hole, and this lane does
not claim one — but a real gap in independent checkability, in exactly the
place ADR-0717 says to look.

**2. `real_lean_creal_carrier_kernel_replay` could not reach a verdict.** It is
registered in `scripts/check-lean-gate.sh` and was SIGABRTing on a stack
overflow before a single Lean ran (`creal` needs 16 MiB in debug; a `#[test]`
thread has 2 MiB). Measured with `RUST_MIN_STACK` unset, so not one-shell
contamination. Wrapped in `on_a_deep_stack`, it now reaches Lean and fails on
finding 1, because its claim is over the *whole* carrier.

Detail moved to [`../notes/386-l0-s4-independent-replay.md`](docs/plan/notes/386-l0-s4-independent-replay.md).

**Status: landed.** ADR-0653's adjacency rule was prose that no code enforced.
It is now `guard()`'s **R11**, backed by `scripts/check-holdout-adjacency.py`,
registered in both aggregate gates, and it refuses the exact draw
[ADR-0762](docs/research/09-decisions/adr-0762-draw-8-is-declined-one-constant-cannot-open-a-draw-and-the-guard-has-no-adjacency-screen.md)
measured as passing. Decision:
[ADR-0768](docs/research/09-decisions/adr-0768-the-adjacency-rule-becomes-r11-and-covers-one-of-three-contamination-shapes.md).
Every measurement, and how to re-run it:
[notes](docs/plan/notes/387-holdout-adjacency-screen.md).

Reproduced independently before building anything — real `select` + `guard`,
in memory, nothing written:

    before  A  GUARD PASSED -- 340 entries, 120 held-out rows
               NEW held-out: ['natural-bitwise-core', 'natural-gcd-basic']
    after   A  REFUSED: R11 2 new held-out family/families publish mathematics
               a development/train family already publishes (ADR-0653)
    control D  three families -> REFUSED at R5, before and after

**Covers** topical overlap outright (`natural-gcd`, and the ADR-0762 draw).
**Partially** covers a differently-named theorem: `natural-parity` is refused,
but through sibling adjacency rather than statement comparison. **Does not**
cover a definition that decides rows by reduction — `fermat-numbers` measures
4/10, under the allowance, and passes; that is
`check-holdout-closed-evaluation.py`'s job. `natural-binomial` and
`natural-divisibility` are also missed, and the notes say why.

Calibrated in both directions, because with three draws declined a screen that
refuses everything would look exactly as correct as one that works: **all 11
standing held-out families stay clean** across draws 0–7, while development and
train families measure 10/10 on the same signal. Draws 5 and 7 pass; draw 6
added no families.

25 tests, 18 mutations across two suites, **zero survivors**, both exit 0. Six
tests are false-positive controls and three mutations target them.

`check-autogenesis-holdout-isolation.py` →
`held_out=116 files_scanned=1109 settled=0 references=0 PASS`. **Nothing
held-out was touched, reclassified or dispatched**, and no file under
`artifacts/facts/` was written by this lane.

Two reds on this tree are **not** this lane's and are characterised in the
notes: `gen-autogenesis-nursery-refill.py --check` (two totient fact statements,
red at the merge-base, `e79804fdd`/`bab6a4a8d`) and one shell-control orphan
from `279081ea9`.

**Next.** Shape 3 is the open one: `is_closed_evaluation` requires a
binder-free statement, so `∀ (a : ℕ), Nat.nthRoot 0 a = 1` is invisible to it —
which matters for the `Nat.nthRoot` draw-9 candidate specifically.

Lane: `l0-s2-trust-circularity`
Phase: ADR-0717 L0, roadmap phase **S2** — complete.
Decision: [ADR-0771](docs/research/09-decisions/adr-0771-trust-and-circularity-are-read-from-the-admitted-term-and-the-identity-map-is-derived.md)

## Status

S2's exit criterion is met and gated. `scripts/check-trust-closure.py` reads the
whole constructed declaration surface out of `kernel_declaration_projection` —
one build reused for every check — and audits every kernel-route settled fact
against its own transitive `Kernel::declaration_dependencies` closure, never
against authored `depends_on`. Registered in both `scripts/check.sh` and the
justfile, together with its control suite.

**No fact was edited.** No `epistemic_status`, `proof_route`, `axiom_footprint`
or `formal.statement` was touched; `git diff main...HEAD -- artifacts/facts/` is
empty. `check-autogenesis-holdout-isolation.py` reports
`held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS`.

## Coverage

    TRUST_CLOSURE|declarations=2482|identity_classes=15|kernel_facts=2041|
      subjects=1956|unresolved=85|absent=0|disclosed_equivalent_pairs=13|failures=0

**1,956 subjects of 2,041 kernel-route settled facts (95.8%)**, against S0's
measured `circularity 38 / 2117`. The remaining 85 resolve to no kernel
declaration and are reported as unenforced rather than assumed correct; the
pinned coverage ratio stops that number growing quietly.

Subject identification adds `evidence[].kernel_declaration` between
`formal.kernel_theorem` and the regex fallback, which closes the primed-name gap
`check-fact-depends-derived.py`'s own comment predicted: that regex excludes an
apostrophe, and `F:nat-bitwise-bit`'s subject is `Nat.bitwise_bit'`, so
extraction yielded a name no declaration bears. The regex itself is imported,
not copied — it carries five measured corrections that must not drift.

## The four mutations and the four guards

| mutation | guard that rejected it | what that guard looks at |
|---|---|---|
| target injection | `guard_self_occurrence` | identity of the subject |
| indirect target injection | `guard_alias_occurrence` | the derived identity map |
| axiom insertion | `guard_forbidden_trust` | declaration KIND in the closure |
| checker-population deletion | `guard_population` | **no closure at all** |

Four different guards, and each looks at something the others do not. The fourth
exists because the other three cannot fail when there is nothing to check.

## Kill sets — 15 mutations, each killing exactly one, ZERO survivors

    baseline: 17 case(s) behaved
    TRUST_CLOSURE_CONTROLS|cases=17|mutations=15|not_exactly_one=0

Detail moved to [`../notes/388-l0-s2-trust-circularity.md`](docs/plan/notes/388-l0-s2-trust-circularity.md).

Lane: `carrier-replay-overclaim`. Decision:
[ADR-0775](docs/research/09-decisions/adr-0775-the-non-prop-residue-is-a-recorded-boundary-not-a-silent-exclusion.md).
Follows L0/S4's census ([386](docs/plan/status/386-l0-s4-independent-replay.md), ADR-0760),
which found this.

## Status

Landed. `F:lean-kernel-accepts-the-whole-constructed-real-carrier` claimed
pinned Lean's kernel accepts EVERY declaration of the constructed-real carrier.
It does not. The statement is narrowed to what is measured, the superseded one
is preserved three ways including as a test that fails if it ever becomes true
again, and the 73 declarations it no longer covers are a typed, named, counted
boundary plus their own OPEN ledger row.

## The measurement

One run, pinned Lean 4.30.0 (`d024af09`), whole `creal` carrier, all four tests
green in 146 s:

    AXEYUM-CREAL-CARRIER counts_agree population=2058 representable=1985
      lean_kernel_constants=1985 non_representable=73
    AXEYUM-CREAL-CARRIER superseded-claim-refuted
      rejected_by_lean=CReal.weierstrassMTest reason=theorem-type-not-prop
      theorem_type_not_prop=48
    AXEYUM-CREAL-CARRIER tampered-proof-rejected subject=CReal.Equiv.not_zero_one
    AXEYUM-CREAL-CARRIER residue-typed population=2058 representable=1985
      theorem_type_not_prop=48 blocked_by_dependency=25 untyped=0

S4 measured the same residue (48 + 25) at population 2,045 / representable
1,972; the carrier grew between the runs, the residue did not.

**Nothing was proved wrong.** `Lean.Environment.addDeclCore` refuses a
`theorem` whose type is not a `Prop`; this kernel has no such rule and uses the
freedom deliberately (`CReal.UniformConvergesOn` is `Type`-valued so a
convergence rate is data). Lean refused a KIND, never a proof. What it was is
73 declarations of the flagship carrier holding no independent-replay grade
with nothing in the ledger saying so.

## What changed, and how the old statement survives

Detail moved to [`../notes/389-carrier-replay-overclaim.md`](docs/plan/notes/389-carrier-replay-overclaim.md).

**Your lane's block (`DONE for this slice`, l0-s5-kernel-differential,
2026-08-30).** S5's exit criteria are met for a first, real slice: a
32-case (4 per subsystem × 8 named subsystems) Axeyum-vs-pinned-Lean
differential corpus, gated, and an 8-mutation kernel-source kill table.
Full writeup: ADR-0780.

What landed:
- `crates/axeyum-lean-kernel/tests/kernel_differential.rs`: 32 cases, each
  authored twice independently (kernel term-builder API + plain Lean
  syntax). Classification is three-way (agree / P0 / registered
  incompleteness); `EXPLAINED_INCOMPLETENESS` has exactly one entry
  (`quotient::quot_sound_absent`, ADR-0456).
- `scripts/check-kernel-differential.py`: the gate, six independently
  mutation-verified guards (`scripts/tests/test-kernel-differential-gate.sh`).
- `artifacts/kernel-differential/mutant-kill-table.json` +
  `scripts/check-kernel-differential-mutants.py`: 8 hand-run kernel-source
  mutations (one per subsystem), 4 killed / 4 survived. The ratchet checks
  the artifact's internal consistency, not a live re-mutation (that needs
  ~8 kernel rebuilds mutating tracked source, which is a by-hand act, not a
  CI-suitable one -- see ADR-0780's alternatives section).
- Registered in `justfile` (`kernel-differential` recipe, added to `check`)
  and `scripts/check.sh` (three `step`s); `scripts/check-lean-gate.sh`'s
  suites table and `CHECK_FLOOR` (229 -> 261) updated -- `check-kernel-
  suites.sh --list`'s auto-discovery had correctly flagged the new suite as
  unregistered before this.

Full run against pinned Lean 4.30.0: 32/32 cases, zero P0, zero unexplained
incompleteness. Two real construction bugs were caught and fixed while
building the corpus itself (a de Bruijn depth error in a parametric
inductive; a `close_pi`-for-a-value confusion in a quotient case) -- see
ADR-0780's evidence section.

Detail moved to [`../notes/390-l0-s5-kernel-differential.md`](docs/plan/notes/390-l0-s5-kernel-differential.md).

**Executable curriculum (`WIP`, book-executable-curriculum, 2026-08-30).**
Build the semantic and evidence layers required by *Instruction Sets,
Programs, and Proofs*. The first slice adds the `axeyum-machine` boundary and
complete A0 concrete execution. Next: independently pinned RV64I and x86-64
teaching slices, broader semantic relations, manifests, Python projection, and
clean-checkout book gates. A0 addition now has fixed-width symbolic certificates;
do not generalize them into an arbitrary-width theorem. Do not describe future
interfaces as implemented until those routes run and their controls fire.

Detail and older landed rows moved to [`../notes/391-book-executable-curriculum.md`](docs/plan/notes/391-book-executable-curriculum.md).

**WIP (autogenesis-knowledge-overlay, 2026-08-24).** A backward-compatible version-1 sidecar joins existing facts and operations to reusable capabilities and pinned read-only `math-education` concepts or techniques.

F1 is complete: the two authoritative multi-target operations have nine applicable facts, all nine have explicitly partial concept/encounter mappings, and seven evidence credits are checked against their fact records (the other two were settled by earlier one-target operations).

The owning fact, operation, claim, and kernel schemas are unchanged; local/external endpoints and false complete-coverage or uncredited-producer edges are mutation-tested.

F2 now projects 1,142 current kernel declarations and 4,127 direct theorem dependencies from accepted terms, with theorem/definition/inductive/constructor/recursor kinds and prelude visibility kept distinct.

Next: normalize producer declines into typed, measured obstructions rather than hand-authoring the next bottleneck.

F3 now normalizes 47 retained decline records into 20 families while preserving unknown remedies and unbound resolutions; next is representation/transport lineage.

F4/F5/F6 now publish hash-bound transport coverage, non-authoritative scheduler observations, and a capability-gap projection.

Live frontier evidence is the limiting result:

141 facts are dependency-ready but zero are admissible because none has a registered applicable operation.

Detail and older landed rows moved to [`../notes/40-autogenesis-knowledge-overlay.md`](docs/plan/notes/40-autogenesis-knowledge-overlay.md).

**Status:** Exact Mathlib 4.30 `Nat.fib_gcd`, `Nat.fib_dvd`, `Int.fib_natCast`, `Int.fib_add_two`, both recurrence corollaries, `Int.fib_neg`, `Int.gcd_fib`, `Int.fib_dvd`, `Int.fib_of_nonneg`, `Nat.fib_pos`, `Nat.fib_eq_zero`, and now `Int.fib_eq_zero` are durably proved with empty kernel footprints. An isolated clean replay independently reproduced `Int.fib_eq_zero` selection, certified execution, exit-75 recovery, exactly one ledger write, its proved fact, and the preregistered empty readiness delta.

**Next:** preregister exact `Int.fib_add` specialization over sealed recurrence uniqueness, exact constructive induction, admitted `Int.fib_add_two`, and the smallest clean algebra/base-value supports.

Detail and older landed rows moved to [`../notes/40-autogenesis-program.md`](docs/plan/notes/40-autogenesis-program.md).

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
*(`Rat.abs` has since landed; this status entry is a historical record.)*
<!-- was-absent: Rat.abs -- since landed -->

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

Detail and older landed rows moved to [`../notes/99-capability-assurance.md`](docs/plan/notes/99-capability-assurance.md).

**ADR-0601 SS2+SS3 landed (`WIP`, adr601-impl, 2026-08-27).**
`scripts/validate-facts.py` now classifies every `cas-certificate` fact's
evidence by what its `checker_command` actually executes
(`classify_cas_certificate_checker`/`classify_cas_certificate_fact`):
`kernel-reconstructed` (a `cargo test`/`cargo run` segment names
`axeyum-lean-kernel`) vs `cas-internal` (only `axeyum-cas`). An unclassifiable
checker on a `cas-certificate` fact is now a validation error — the
checker-that-cannot-fail defect one level up. Measured on the current ledger:
`cas-certificate: 23 total -- kernel-reconstructed 0, cas-internal 23`,
printed in both the summary's per-route line and its own dedicated line.
`python3 scripts/validate-facts.py` stays green: 776 facts, 0 errors.

`scripts/gen-import-backlog.py` (new) turns the validator's bare "164 settled
elsewhere but not here" count into a produced, deterministic artifact,
`artifacts/import-backlog.json`: 164 rows, 117 `dependency_ready`, 1
`curriculum_node`-mapped (the curriculum-mapping is an EXACT match on
`concept_refs[].graph == "math-education"` against a `curriculum.toml` node
id — see `docs/autogenesis/289-import-backlog-artifact.md` for why this is
exact rather than fuzzy, and why the mapped count is small and honest).
`--check` mode mirrors `gen-plan.py --check`'s convention; registered in
`scripts/check.sh` and the `justfile` next to `gen-adr-index.py --check`.
`scripts/fact-frontier.py` was NOT touched (owned by a concurrent lane).

Both new classifiers are mutation-tested via
`scripts/tests/mutation_controls.py` (`fact-cas-certificate-classification`,
`import-backlog-classification`), each guard confirmed to kill exactly one
test.

Not done: no attempt was made to extend the `math-education`↔`curriculum.toml`
crosswalk beyond the 4 ids that already coincide exactly — that would need a
maintained mapping table this task's scope did not include, and a fuzzier
matcher would manufacture edges nobody asserted.

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

**Gap #1's one confirmed fix is landed, in the form its diagnosis said to ship
it in: minimisation is budget-driven, not width-gated** (`WIP`,
agent-lia-core-minimisation, 2026-08-21). `dpll_lia.rs` had one constant doing
two jobs — deciding whether a theory conflict core was minimised at all, and
deciding which cores are charged against the wide-clause retention budget. The
[diagnosis](docs/research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md)
§5.2 measured what that costs: the cores too wide to minimise are exactly the
cores whose width then exhausts the retention budget, so a solve declines for
want of the narrow clauses it refused to narrow. The jobs are now separate —
`MINIMIZATION_ORACLE_CALL_BUDGET` (a deterministic **oracle-call** ration, chosen
over wall clock because determinism is a public API promise) admits the pass;
`WIDE_THEORY_CORE_ATOMS` (still 128) only decides retention accounting, by
**retained width** rather than by provenance, which keeps the memory protection
the naive constant bump gives up.

Measured on the pinned 200-file competition lists, three binaries plus z3 4.13.3
run **adjacent in time per file** so contention is shared across the arms:

| division | base | A/B (128→4 096) | **shipped** | vs z3 | vs declared `:status` |
|---|---:|---:|---:|---|---|
| **QF_UFLIA** | 92 | 112 | **114 (+22, −0)** | **0** disagreements / 114 | **0** / 114 |
| QF_IDL (control) | 66 | 66 | **65 (+0, −1)** | **0** / 63 | **0** / 65 |

Detail moved to [`../notes/agent-lia-core-minimisation.md`](docs/plan/notes/agent-lia-core-minimisation.md).

**Ranked gap #1 is diagnosed: three causes, not one, and the largest single
block of losses is a route that quits at 5 % budget use** (`WIP`,
agent-lra-diagnosis, 2026-08-21). Measured at `8426fbd2d` over the four pinned
200-file competition lists (sha256 unchanged from their `PARITY.md` entries),
axeyum + z3 4.13.3 at 24 s each, then a second pass for route ladders. cvc5 is
not installed on this host; z3 lands within 5 files of cvc5's recorded count in
every division, which is why it is used to decide which failures count.
Instrument validated by reproducing QF_LRA's recorded 86/200 exactly.

278 misses classify as: **T** budget exhausted 146, **S** admission decline on a
size constant 73, **I** incompleteness 48, **P** front-door reject 11. The
route ladders say these are **three** causes, and they do not line up with the
divisions:

- **`dl-online` runs out of clock** — 64/65 QF_IDL and 51/55 QF_RDL misses. The
  one genuinely shared cause, and it is shared by two divisions, not four.
- **the LRA route** — QF_LRA (and QF_RDL's tail): half refuse on
  `MAX_ONLINE_LRA_ATOMS = 1_024`, half time out.
- **the lazy UF/arith CEGAR** — QF_UFLIA, **82 of 82** traced misses, one route.
- plus **26 QF_UFLIA files rejected at the parser** for `Int` literals beyond
  `i128` (the Certora/EVM family, 2^256 constants). A capability zero, 13 % of
  the division, untouched by any solver work.

Two one-constant A/Bs, built in a private snapshot, positive-controlled, never
in the shared tree:

- **REFUTED** — making the LRA atom cap fall through instead of terminal
  (`lra_theory.rs:203`): **0** new decides over 71 files and **54** memory
  aborts past 12 GiB. The cap is load-bearing protection; both routes are
  inadequate above ~1,000 atoms.
- **CONFIRMED** — `MAX_MINIMIZED_THEORY_CORE_ATOMS` 128 → 4 096
  (`dpll_lia.rs:48`). QF_UFLIA **92 → 109 (+17)**, QF_IDL 65 → 64 (the one loss
  re-decides on a quieter box on **both** binaries), **0 disagreements** against
  z3 and **0** against the declared `:status`. The 48 QF_UFLIA `I1` files return
  `unknown` after a median **1.3 s of 24 s** with `core_src_minimized=0` — the
  cores too wide to minimise are exactly the cores whose width then exhausts
  `MAX_DYNAMIC_LARGE_CORE_LITERALS`.

Detail moved to [`../notes/agent-lra-diagnosis.md`](docs/plan/notes/agent-lra-diagnosis.md).

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

**Both gap-analysis §7 defects closed, and both were worse than the audit
recorded them** (`DONE`, agent-resource-guards, 2026-08-21).

Detail moved to [`../notes/agent-resource-guards.md`](docs/plan/notes/agent-resource-guards.md).

**Two of the three string-length certificates now carry a Lean term real Lean 4
accepts; the third declines for two independent reasons, and the guard that was
supposed to catch the second admitted it** (`WIP`, string-recon, 2026-08-20).

`Evidence::UnsatStringLength` was rung 2 of the ladder — a certificate an
independent checker re-derives, with nothing kernel-checked behind it.
`reconstruct_string_length` builds the term for the **conjunctive** case over
the constructed integers (`try_new_over_integers`; `integer: axiom=0`), not
`AxReal` and not `CReal`: lengths and code points are integers, and `ℤ` models
every law a Farkas combination uses.

Detail moved to [`../notes/agent-string-recon.md`](docs/plan/notes/agent-string-recon.md).

**Task 1 `DONE` (2026-08-27), 0 of 15 facts closed — a measured negative
result, not a failure.** Brief: extend `trusted_substitution`/
`nat_order_substitution`'s allowlist to cover `Nat.mod_lt`/`eq_self` (doc
294's estimate of the remaining gap for doc 292's 15 `Nat.Coprime`
`TrustedDeclaration` declines) and re-run the real failing exports.

Measured, not estimated, via a standalone NDJSON decoder against doc 292's
own s5 exports plus the real `statement_goal_record` binary: doc 294's "two
names" estimate undercounts the real closure. The smallest representative
fact needs **15** additional theorem-kind names beyond existing coverage,
not 2 — 7 are generic `WellFounded.fix`/eager-fixpoint internals (a
different, larger construction class `nat_order_substitution`'s technique
doesn't cover), the rest are ordinary order lemmas needing a `Nat.beq`
primitive that module doesn't yet discover. `eq_self` independently needs
`propext`, which this kernel deliberately excludes (intuitionistic design,
`prelude.rs:61`) — architecturally permanent, not deferred engineering.

**Split of the 15**: 1 permanent (`Quot`, hard rule, unchanged from doc
294), 5 permanent (need `propext`), 9 deferred (need the WF-recursion
cascade — real, doable, substantial future engineering, not attempted here
per the brief's own stop condition). 0 closed. No changes made to any of
the four substitution modules — nothing was safely addable within a
reviewed scope. Guard mutation test reproduced doc 294's result exactly (3
tests red with the whole-stream `matches!` guard neutered; restored clean).
Full writeup: `docs/autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md`.

Detail moved to [`../notes/allowlist-clippy.md`](docs/plan/notes/allowlist-clippy.md).

**Your lane's block (`DONE`, blocked-mirror-divergences, 2026-08-30).**

Resolved as much of each of the four `check-dispatchable-frontier.py`
"structurally blocked by a divergence" causes as is honest, landing two new
kernel theorems and correcting one stale sizing (ADR-0840). No mirror was
flipped (none of the four should be).

## `Nat.testBit` (codomain) — 5 facts, 2 already done, 2 landed this lane, 1 stays deeply blocked

- `F:ml430-nat-lt-of-testbit-72f64ab8`, `F:ml430-nat-zero-of-testbit-eq-false-e244c9a1`:
  **already resolved by prior lanes** (`F:nat-lt-of-testbit`,
  `F:nat-zero-of-testbit-eq-zero`, both `proved`, axiom-free). Verified in
  tree, nothing further needed.
- `F:ml430-nat-testbit-land-dfef7ca4`, `F:ml430-nat-testbit-lor-7644e067`:
  **landed this lane** as `F:nat-testbit-land` and `F:nat-testbit-lor`
  (`crates/axeyum-lean-kernel/src/nat_prelude/testbit_bitwise.rs`), both
  admitted axiom-free, each with a concrete discriminating instance (3
  bits) plus a symbolic check. Transported `testbit_bitwise.rs`'s existing
  `Nat.testBit_xor` technique (induction on the bit index, reduced to a
  low-bit lemma and a div-by-2 lemma per level) to `landAux`/`lorAux`
  directly. One real bug found via a temporary `render_lean` debug probe:
  `land_div_two`'s `at_n_zero` branch assumed `land_zero_right(m) : Eq
  (land m 0) m` (copying `lor`'s shape); `land`'s absorbing zero means it is
  actually `Eq (land m 0) 0` on BOTH sides. Fixed; `lor`'s construction
  (byte-for-byte from `xor`'s shape, since `lor`'s boundary behavior is
  identical to `xor`'s) was admitted on the first attempt.
- `F:ml430-nat-testbit-eq-inth-ffa07392`: **stays open, genuinely deeper
  blocked than the other four.** Needs `n.bits : List Bool` +
  `List.getI`; this kernel has **no `List` type at all**, on top of the
  Bool/Nat codomain mismatch. No local analogue attempted — there is no
  honest Nat-valued restatement of "the i-th element of a list this kernel
  cannot construct."

Detail moved to [`../notes/blocked-mirror-divergences.md`](docs/plan/notes/blocked-mirror-divergences.md).

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

**Landed and green** (`WIP`, creal-steps, 2026-08-27). Applied the spike's
level 1 ([2026-08-27-prelude-build-spike.md](docs/research/11-design-review/2026-08-27-prelude-build-spike.md))
to `crates/axeyum-lean-kernel/src/creal.rs`, exactly as recommended: one
`BuildStep` per top-level call in the existing 135-call
`build_creal_prelude_uncached` sequence (441 `CRealPrelude` fields; a
module's internal `declare_*` helpers fold into their module's single
dispatch entry, same granularity `poly.rs` used in the `complex.rs`
prototype). No field moved out of `CRealPrelude` — Part B stays explicitly
out of scope here, per the spike's own ~8,997-call-site estimate for a full
module split.

Headline: `validate_step_order` finds **0 violations across 2,264
requirement edges** against the existing hand-written order — it was
already topologically valid, same result as the `complex.rs` prototype.
Every one of the 443 fields is provided by exactly one step (0 duplicates,
0 gaps), confirmed by the extraction's own self-consistency check before
generating the table.

Detail moved to [`../notes/creal-steps.md`](docs/plan/notes/creal-steps.md).

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

Detail and older landed rows moved to [`../notes/creal.md`](docs/plan/notes/creal.md).

**Verification throughput was the binding constraint, and the cause was
scheduling rather than any gate** (`landed`, gate-throughput, 2026-08-27). The
`hooks/pre-push` battery went from ~250 s uncontended to **2,152 s / 2,654 s**
under 4-5 lanes, inflated 4.0-6.8x roughly uniformly across kernel suites,
corpus sweep, solver unit sweep and golden pins. Uniform inflation across
unrelated steps is starvation, not a regression.

Detail moved to [`../notes/gate-throughput.md`](docs/plan/notes/gate-throughput.md).

Status: DONE for this session. One complete graded family landed (rows 1
+ 3, row 2 argued absent), both declarations axiom-free, both facts
registered and validated, ADR-0825 records the reasoning. Family B was
NOT attempted -- see "Why only one family" below.

## Step 0 findings — what already exists (read this before assuming anything below is open)

- **ADR-0716 is accepted** and settles the framing: for Nat/Int/Rat the
  analysis-style row 2 (order totality) is a proved, axiom-free theorem, so
  it is EMPTY for number theory. Two other boundaries survive (unbounded
  search / LNP-implies-EM, and an expressiveness row 2'). Per this lane's
  brief, row 2 is out of scope here regardless.
- **The unrestricted LNP-implies-EM row 2 is ALREADY LANDED**, by a sibling
  lane, committed and merged to `main` before this lane started:
  `nat_prelude/least_number.rs::declare_lnp_unrestricted_implies_em`
  (commit `b81277a5c`, "the unrestricted least-number principle IS excluded
  middle"). Do not rebuild this.
- **Euler's theorem (`a^phi(n) = 1 mod n`) is NOT close**, contrary to
  ADR-0716's "one theorem away" framing, which is itself corrected by a
  sibling lane's own handoff: `docs/plan/status/374-euler-theorem.md`
  (status: PARTIAL) plus `int_prelude/euler_theorem.rs`'s module doc, both
  landed and merged (`f0453c65f`). `Int.prodRangeIf`/`Int.prodRangeIf_permute`
  are landed; three more genuinely hard pieces remain (Nat/Int index
  bridging, the IFF-converse of `euler_unit_coprime`, and final assembly).
  Not attempted by this lane — too large a bite alongside a second family,
  and actively claimed by another lane's handoff.
- **The classical Euclid-Euler even-perfect-number theorem (Euclid IX.36) is
  under ACTIVE multi-lane construction** in
  `nat_prelude/perfect.rs` (3702 lines as of this session; commits include
  "step 4 of the Euclid IX.36 chain", "Euclid IX.36's family non-overlap",
  etc., all recent and merged). `Nat.sumDivisors`, `Nat.Perfect`,
  `Nat.sumDivisors_two_pow`, `Nat.dvd_two_pow_mul_classify` are landed;
  `declare_perfect_all` does not yet wire up the full Euclid IX.36 result.
  **Not touched by this lane** — high collision risk with active work, deep
  existing proof architecture not worth re-deriving in one session.

Conclusion: picked a family away from the three hot areas above, using
already-landed but currently-unconnected infrastructure.

## Family A (landed): Fermat's little theorem, contrapositive form — a computable compositeness certificate

Detail moved to [`../notes/graded-families-number-theory.md`](docs/plan/notes/graded-families-number-theory.md).

**Done (`DONE`, graded-families, 2026-08-27).** Stated the four rows —
constructive general form, boundary refutation, exact decidable-fragment
form, labeled import — for MVT, LUB/completeness, Taylor remainder, and FTA
(the four theorems the 2026-08-27 architecture review §4 named as owed this
treatment, IVT/EVT already having it). Deliverable:
[`docs/curriculum/graded-statement-families.md`](docs/curriculum/graded-statement-families.md),
linked from `spivak.md` (rows 8, 11, 20, 25–27) and from ADR-0603.

Measured with `prelude_theorem_inventory --release --include-constructed`
(theorem rows) and `kernel_declaration_projection --require-declaration`
(definitions; exits non-zero on absence), both rebuilt fresh this session
(`scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
prelude_theorem_inventory --example kernel_declaration_projection`), plus
`cargo test -p axeyum-cas --lib extremum::` (20 passed) and
`python3 scripts/validate-facts.py` (806 facts). Every negative was paired
with a positive control of the same declaration kind before being trusted.

**Headline findings** (see the doc for full citations):

Detail moved to [`../notes/graded-families.md`](docs/plan/notes/graded-families.md).

**Closed five of doc 292's eleven declined `Int.ModEq` facts** (`DONE`,
int-modeq-kernel, 2026-08-27). Doc 292's batched flywheel turn declined
eleven unconditional `Int.ModEq` identities with `TerminalNotClosed` — the
combinator-over-hypothesis producer has no congruence step for a fact with no
hypothesis to combine. This lane proved a new general kernel theorem,
`Int.modEq_add_mul_left : ∀ n a q, ModEq n (add (mul n q) a) a`, unconditional
in `n` (case-split on `n`'s `Int.rec` shape: `0` trivial via the `emod`
zero-identity; positive via the existing `Int.modEq_iff_dvd` bridge at one
concrete shape; negative reduced to the positive case via the already-proved
`Int.modEq_neg_modulus`/`Int.emod_neg` pair — no new magnitude bound needed
anywhere), plus five direct corollaries: `Int.add_modEq_left`,
`Int.add_modEq_right`, `Int.mod_modEq`, `Int.modulus_modEq_zero`,
`Int.modEq_sub`. All six are `Kernel::add_declaration`-checked `Theorem`s with
empty `axiom_footprint`. Full account:
[`docs/autogenesis/293-int-modeq-unconditional-shift-family.md`](docs/autogenesis/293-int-modeq-unconditional-shift-family.md).

Five facts flipped `open` → `proved`
(`F:ml430-int-add-modeq-left-ee732b5b`, `F:ml430-int-add-modeq-right-e58108ee`,
`F:ml430-int-mod-modeq-6bec7847`, `F:ml430-int-modulus-modeq-zero-5b57a898`,
`F:ml430-int-modeq-sub-3148f130`), each with three evidence rows (statement
pin, axiom footprint, concrete corroboration at `n := 0`, `n := 5`, `n := -4`,
mutation-verified in an isolated snapshot). The corresponding five decline
artifacts were AMENDED (not deleted, doc 291's convention) with the later
admission and the actual route.

Detail moved to [`../notes/int-modeq-kernel.md`](docs/plan/notes/int-modeq-kernel.md).

**Status:** COMPLETE — all four ADR-0780 mutant survivors closed. Kill table is
8 killed / 0 survived over a 35-case corpus. No P0 in the unmutated kernel.

Decision: [ADR-0815](docs/research/09-decisions/adr-0815-a-mutation-aimed-at-a-call-site-cannot-see-a-shared-predicate.md)

## What this lane was for

ADR-0780's kernel differential found zero Axeyum-accepts/Lean-rejects
disagreements, which is the result we wanted, and then mutation-tested the
kernel itself and had **four of eight mutants survive**. A survivor means a
soundness guard was removed and the differential did not notice. The
`inductives` one was unexplained, which made it the most important open item
in L0 — ADR-0717's risk 1 is exactly "our own kernel could have a shared
semantic defect", and this was a place where we removed a check and the
detector shrugged.

## Headline

**All four had one cause between them, and it is not a corpus weakness.**
Three of the four (`inductives`, `projections`, `quotient`) were killed by a
SECOND guard implementing the same predicate at a different call site; only
`literals` was a genuine missing case. A mutation aimed at a call site cannot
be killed when a redundant implementation still rejects — and the fix is to aim
at the predicate, not to write more cases.

### `inductives` — outcome 1: a different real guard rejects

Five measured rebuilds, `--release`, in this worktree.

| # | kernel state | `add_inductive(Bad, …)` |
|---|---|---|
| E1 | unmutated | `Err(NonPositiveInductiveOccurrence)` |
| E2 | positivity `Err` off (`inductive.rs:1933`) — ADR-0780's mutation | `Err(ReflexiveOrNestedNotSupported)` |
| E3 | field-shape classification off (`inductive.rs:2076`) | `Err(NonPositiveInductiveOccurrence)` |
| E4 | **both off** | **`Ok(())`** — P0 |
| E5 | shared predicate `mentions_group_family` `Const` arm → `false` | **`Ok(())`** — P0 |

E1 rules out the possibility ADR-0780 could not: the case does reach the
targeted guard. E2 names the taker-over. E3 shows symmetry. **E4** proves the
pair is jointly load-bearing rather than both being decoration. E5 is the
correctly-aimed single mutation and it KILLS.

`check_group_positive_occurrence` and `open_group_recursive_field_shape` are
the same algorithm written twice; one returns `Some` exactly where the other
returns `Ok`. **No case can separate them** — that impossibility is the
finding, not a corpus gap.

### Survivors closed, and the mutant each new case kills

Detail moved to [`../notes/kernel-mutant-survivors.md`](docs/plan/notes/kernel-mutant-survivors.md).

**Closed the "no shape for hand-authored kernel proof" gap doc 293 hit**
(`DONE`, kernel-receipt, 2026-08-27). Doc 293 proved five `Int.ModEq`
theorems directly against the kernel (no producer/import pipeline component
running at all) and could not register the retrospective receipt ADR-0602
calls for: `validate-autogenesis-operations.py`'s `EXECUTION_DRIVERS` was a
closed set of ten, eight of them `axeyum-lean-import/*` (pipelined) and two
named for one-off episodes. Per doc 288, 125 of 132 dependency-ready facts
are exactly this `proof-route-only` shape, so this was not a corner case.

Added `axeyum-lean-kernel/authored-declaration-v1` in
`scripts/validate-autogenesis-operations.py`: fields chosen to be
independently re-checkable (declaration name(s), the source file each must
literally appear in, and the exact test functions that must exist and fail
on their absence) rather than narrative. Registered doc 293's five closures
as ONE operation (`authoritative-kernel-int-modeq-shift-family-v1`) naming
all five facts, per the standing "`applicability.fact_ids` is a list, never
required length one" rule (doc 228). Full account:
[`docs/autogenesis/296-a-general-kernel-lane-execution-driver.md`](docs/autogenesis/296-a-general-kernel-lane-execution-driver.md).

Detail moved to [`../notes/kernel-receipt.md`](docs/plan/notes/kernel-receipt.md).

**Done, l0-s6-credit-transaction, 2026-08-30.** [ADR-0785](docs/research/09-decisions/adr-0785-credit-transactions-two-phase-commit-with-a-crash-sweep-that-actually-crashes.md)
records the full measurement. Summary:

`scripts/credit-transaction.py` is a fault-injectable two-phase-commit engine
over a self-contained fixture ledger (`facts/`, `receipts/`, `pins/`,
`graph/`, `dashboards/`) — deliberately NOT wired into the real
`artifacts/facts/` flip in this phase, since that surface
(`scripts/validate-facts.py`, the real pins file) belongs to other lanes;
scope here was the transaction mechanism and its verification.

Measured, not asserted:

Detail moved to [`../notes/l0-s6-credit-transaction.md`](docs/plan/notes/l0-s6-credit-transaction.md).

**Done, l1-c0-artifact-contract, 2026-08-30.** [ADR-0800](docs/research/09-decisions/adr-0800-the-library-artifact-record-splits-type-and-proof-into-different-files.md)
records the design decisions. Summary:

`artifacts/library-artifact/` freezes the pack record shape from
`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C0:
Lean/Mathlib version+commit identity, per-declaration content digests, four
SEPARATE dependency fields (`direct_type_deps`, `direct_value_deps`,
`transitive_type_deps`, `transitive_value_deps`), derived
`trusted_declaration_identities`, normalization/renderer versions, and a
`source_population` block. A 9-declaration positive pack
(`packs/nat-add-comm-v1.pack.json`: `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`,
`Eq`, `Eq.refl`, `id`, `Nat.add`, `Nat.add_comm`) is hand-authored — real
Lean-core declarations, this contract's own canonical rendering of their
types/values, digests mechanically derived and independently re-derived by
both readers. C1 (`artifact-extract`) owns wiring a real pinned Lean-side
extractor at scale; this phase is the contract those extracted packs must
satisfy, not the extractor.

Measured, not asserted:

Detail moved to [`../notes/l1-c0-artifact-contract.md`](docs/plan/notes/l1-c0-artifact-contract.md).

**G0 exit criteria met (`DONE`, l1-g0-module-baseline, 2026-08-30).**
`docs/plan/graph-directed-library-roadmap-2026-08-30.md` phase G0 asked for a
compact, reproducible receipt of the Mathlib module-import graph without
vendoring a checkout, with source-or-parser drift failing the gate. Both are
in place: [ADR-0805](docs/research/09-decisions/adr-0805-the-module-baseline-receipt-is-a-hash-and-a-parser-not-a-vendored-checkout.md)
records the design and evidence.

`scripts/gen-module-baseline.py` / `scripts/lib/module_baseline.py` parse
`Mathlib/**/*.lean` under whatever checkout `--mathlib-dir` names (default:
the pinned toolchain checkout `scripts/provision-lean-import-toolchain.sh`
provisions, commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`) into a
compact receipt at `artifacts/module-baseline/receipt.json`: source commit +
content tree hash, parser sha256, module/edge totals, top-indegree/outdegree
rows, no-importer sink count.

**This is the full parse over all 8,094 `.lean` files, not a bounded
subset** — it completes in roughly 7-9 s per invocation, so there was no
need to reduce scope. Measured totals match the roadmap's hand-measured
evidence baseline exactly: 8,094 modules, 25,495 internal edges, 1,476
no-importer sinks, `Mathlib.Init` 193 importers, `Mathlib.Tactic.Common` 69,
`Mathlib.Algebra.Ring.Defs` 43, `Mathlib.Tactic` outdegree 336.

`scripts/check-module-baseline.py` re-parses the source TWICE per invocation
(so "two runs reproduce the receipt" is a standing, mechanically-checked
property rather than a one-time human observation) and diagnoses SOURCE_DRIFT
and PARSER_DRIFT as independently-firing reasons — verified by two real
subprocess scenarios, not simulated: a fixture content change with the
commit label held fixed fires only SOURCE_DRIFT; a behaviour-preserving
parser edit (appended comment, same logic, different sha256) fires only
PARSER_DRIFT. Three absence cases (missing directory, no `Mathlib/`
subdirectory, zero `.lean` files parsed) each raise before any receipt is
written.

Detail moved to [`../notes/l1-g0-module-baseline.md`](docs/plan/notes/l1-g0-module-baseline.md).

**Done, l1-g1-declaration-graph, 2026-08-30.** [ADR-0820](docs/research/09-decisions/adr-0820-the-declaration-graph-reuses-the-artifact-contracts-type-proof-separation.md)
records the design decisions.

## What landed

Executed C1 of `docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`
and G1 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`: a real
(not hand-authored) declaration graph over a bounded, named population,
built on ADR-0800's artifact contract and ADR-0805's toolchain provisioning.

Detail moved to [`../notes/l1-g1-declaration-graph.md`](docs/plan/notes/l1-g1-declaration-graph.md).

**Done, l1-g2-join-axeyum-state, 2026-08-30.** [ADR-0835](docs/research/09-decisions/adr-0835-the-graph-join-resolves-identity-only-through-an-existing-ledger-mirror.md)
records the design decisions.

## What landed

Executed G2 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`:
joined ADR-0820's declaration graph (446 declarations, population
`mathlib-group-defs-v1`) to seven dimensions of Axeyum's own state, with
every dimension's population, resolved and unresolved counts reported
explicitly.

Detail moved to [`../notes/l1-g2-join-axeyum-state.md`](docs/plan/notes/l1-g2-join-axeyum-state.md).

**Done, l2-g3-infrastructure-frontier, 2026-08-30.**
[ADR-0845](docs/research/09-decisions/adr-0845-the-infrastructure-frontier-curates-candidates-and-validates-them-live.md)
records the design decisions.

## What landed

Executed G3 of `docs/plan/graph-directed-library-roadmap-2026-08-30.md`:
four frozen queues over the L1 phase G2 graph join
(`artifacts/graph-join/mathlib-group-defs-v1.join.json`, ADR-0835), each
row carrying a stable content-hash id, raw evidence, a stated gain kind,
current blockers, destination paths, an estimated cost, and a
preregistered, re-runnable metric.

Detail moved to [`../notes/l2-g3-infrastructure-frontier.md`](docs/plan/notes/l2-g3-infrastructure-frontier.md).

**DONE (`ledger-duplicate-propositions`, 2026-08-30).** ADR-0771 (S2 trust-closure)
measured 15 identity classes (theorem pairs sharing a byte-identical
`Kernel::render_lean` canonical type), all 15 with both members registered as
ledger facts -- 15 propositions counted as 2,121 proved facts twice. This lane
verified all 15 by hand against `formal.statement` and each proof closure;
**all 15 survived scrutiny as genuine duplicates**, none rejected as "proved
from but strictly stronger." See ADR-0790 for the full breakdown, including
the two pairs (`CPoint.apollonius_from_stewart`/`_median`,
`Int.add_mul`/`Rat.int_right_distrib`) proved **independently** rather than
via one reusing the other's closure.

Facts are never deleted (ADR-0542, restated for facts here as ADR-0790): one
member of each pair now carries a new `equivalent_to: ["F:..."]` field
(`artifacts/ontology/fact.schema.json`), pointing at a canonical survivor.
Both members stay `proved`. `scripts/check-proposition-duplication.py` gates
any NEW unlabeled duplicate pair from entering, and
`scripts/validate-facts.py`'s summary now prints DISTINCT PROPOSITIONS
ESTABLISHED beside FACTS SETTLED so the two numbers cannot be quoted apart
again.

Corrected numbers: **2,123 facts settled** (`proved` 2,121 + `computed` 2),
**15 restate a sibling**, **2,108 distinct propositions established**
overall -- or, matching the original headline's own scope, **2,106 distinct
propositions** among the 2,121 `proved` facts alone.

Nothing else in this repository changed status: no fact's `epistemic_status`
flipped, no held-out nursery row was touched, `scripts/check-trust-closure.py`
(S2's own file) was not edited.

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

**Done** (`WIP`, nursery-partition-leak, 2026-08-30). `check-autogenesis-nursery.py`
went from `EXIT=1` with a bare, un-actionable header to `EXIT=0` naming every
crossing it forgives and why.

Diagnosed independently against `artifacts/autogenesis/nursery-v1.json` (not
inherited from a prior lane's report, which named the wrong facts): **3
declared-dependency components cross train/development, zero held-out
involvement**, plus a 4th/overlapping violation where 8 evaluation facts (7
train, 1 development) share a component with the Autogenesis-1 longitudinal
facts via `F:nat-mul-one`/`F:nat-zero-add`. Root cause: commit `237c1abdd`
(2026-08-29) retroactively added 1,054 real `depends_on` edges the
2026-08-18 freeze never saw. All 18 affected facts are independently verified
`epistemic_status: proved`, zero of the 29 registered autogenesis operations
reference any of them, and none are held-out.

Landed: `describe_leak()` renders every violation with full component/family/
shape/source-group membership and partitions, and `build_report` accumulates
ALL violation types into one message instead of raising on the first. A new
`component_split_exemptions` mechanism (self-invalidating: keyed on the exact
component digest recomputed from the CURRENT dependency graph, so it silently
stops applying the moment an exempted component grows) covers exactly the 3
diagnosed benign crossings, recorded and justified in
[ADR-0850](docs/research/09-decisions/adr-0850-nursery-split-exemption-mechanism.md).
No amendment, no partition move, no fact edit — the crossing was a
bookkeeping gap the ledger-hygiene fix exposed, not a spent evaluation row.

Flagged in the ADR for a decision above this lane's level, not resolved here:
104/120 development and 72/78 train v1 entries are already `proved` against
0/16 held-out — consistent with train/development being meant for ordinary,
non-blind work, but nothing in ADR-0478 says so explicitly and no gate
measures it.

8 new tests added (19 total, all green); 6-guard mutation kill table below
— 5 guards killed exactly 1 test, 1 guard (`leaks` exemption filtering) killed
2 (both legitimately exercise the same suppression path from different
angles; not a vacuous-guard case).

**Status: DONE — draw 9 is AUTHORED. The dispatchable frontier clears its
floor (1 -> 21 against floor 10) with ZERO new kernel constructions**, against
ADR-0762's (draw 8, declined) conclusion that two new construction-only
declarations were required first.

Decision record:
[ADR-0830](docs/research/09-decisions/adr-0830-nursery-draw-9-two-below-floor-held-out-combinations-not-two-new-constructions.md).

## What changed

`scripts/gen-autogenesis-nursery-refill.py`: four new families in
`FAMILY_MODULES`/`FAMILY_ROUTES`.

| family | partition | modules | rows |
| --- | --- | --- | --- |
| `integer-elementary-identities` | held-out | `Init.Data.Int.Basic`, `Init.Data.Int.Compare`, `Init.Data.Int.Linear`, `Mathlib.Data.Int.DivMod` | 10 of 11 |
| `natural-bitwise-basics` | development | `Init.Data.Nat.Bitwise.Lemmas` | 10 of 33 |
| `natural-distance` | train | `Mathlib.Data.Nat.Dist` | 10 of 18 |
| `natural-elementary-bounds` | held-out | 10 small leftover Nat modules (see ADR-0830) | 10 of 12 |

Regenerated: `artifacts/autogenesis/nursery-v2-extension.json` (300 -> 340
entries). 40 new fact files under `artifacts/facts/F-ml430-*.json`.

## Why this route and not ADR-0762's

ADR-0762 measured the un-owned floor at 7 modules, none held-out-safe, and
concluded draw 9 needed two NEW kernel declarations (`Nat.nthRoot` clean, a
second candidate unidentified — `Squarefree` measured and rejected). That
measurement re-derives identically on this tree (`env=2383`, same seven
modules). What ADR-0762 did not check: several modules BELOW the
`PER_FAMILY` floor, already admissible with **zero new declarations**, combine
into a held-out-safe pool the way draws 3/4/5 already did
(`integer-division-boundary-cases`, `range-induction`,
`integer-absolute-value`). Two such combinations exist and both are R9/R11
clean, verified with the real `select()`/`guard()` in memory before being
written — see ADR-0830 for the full reasoning and the exact probe output.

## Screening performed (every family considered, including rejections)

Detail moved to [`../notes/nursery-refill-draw-9.md`](docs/plan/notes/nursery-refill-draw-9.md).

**Done** (`done`, nursery-v2-component-coverage, 2026-08-30). Extended
`scripts/check-autogenesis-nursery.py`'s declared-dependency component-split
check to the union of `nursery-v1.json` and `nursery-v2-extension.json`:
`build_cross_population_report()` found 3 previously-invisible cross-population
component crossings (none held-out) and they are now exempted with full detail
per ADR-0850's mechanism. ADR-0855 records the decision and settles ADR-0850's
open train/development invariant question from the existing record. Full
diagnosis, mutation guard->test table, and open items below.

## Task

`scripts/check-autogenesis-nursery.py` only ever reads
`artifacts/autogenesis/nursery-v1.json` for its declared-dependency
component-split check. `artifacts/autogenesis/nursery-v2-extension.json`
(340 entries) is invisible to it entirely — no v2-internal crossing and no
v1<->v2 crossing is checked anywhere.

## Diagnosis (independently measured, union graph over v1 entries + v2 entries,
adjacency from `artifacts/facts/*.json` `depends_on`, restricted to edges
where both endpoints are in the v1∪v2 selected set)

v1/v2 fact_id overlap: **none** (0 of 556 total ids collide).

Computing weakly-connected components over the **union** surfaces **3**
declared-dependency components that cross evaluation partitions
(train/development/held-out), none involving held-out:

1. `4c696b5744bb...` — 3 members, **entirely within v2**:
   `F:ml430-nat-div-gcd-pos-of-pos-left-dd878a3f` (train),
   `F:ml430-nat-div-gcd-pos-of-pos-right-8d26808c` (train),
   `F:ml430-nat-div-mul-cancel-99799a00` (development).
2. `510e9696bc85...` — 206 members, **v1 ∪ v2 merge**. This is v1's THREE
   ADR-0850-exempted components (`de94125d520a`, `6959be9c08c2`,
   `533d01fc3b24`, all train/development, previously the entire finding of
   ADR-0850) merged with TWO v2-internal crossing components
   (`aee5f7b663cc`, `11b9f2566178`) into one component, via real declared
   dependency edges between v1 and v2 facts (`int-gcd`/`int-dvd`/`nat-choose`/
   `nat-coprime`/`nat-factorial` families chain together). Also touches the
   two longitudinal Autogenesis-1 facts (`F:nat-mul-one`, `F:nat-zero-add`),
   same as ADR-0850 already found for the v1-only version of this component.
3. `55e86f8aed26...` — 4 members, **v1 ∪ v2 merge, newly visible only in the
   union** (does not appear as a crossing in v1-only OR v2-only analysis):
   `F:ml430-int-modeq-add-left-cancel-062ad5fe` (v1, train) plus three v2
   development entries (`...-c1adde5a`, `...-d7366811`, `...-f74acb64`).

Detail moved to [`../notes/nursery-v2-component-coverage.md`](docs/plan/notes/nursery-v2-component-coverage.md).

**Prototype landed and green** (`WIP`, prelude-spike, 2026-08-27). Built the
level-1 phase-order fix and the level-2 topological-order validation from
[2026-08-27-architecture-review.md](docs/research/11-design-review/2026-08-27-architecture-review.md)
§1 on `crates/axeyum-lean-kernel/src/complex.rs`, plus a real (not simulated)
Part B module-registry split for `complex/poly.rs`. Full writeup:
[2026-08-27-prelude-build-spike.md](docs/research/11-design-review/2026-08-27-prelude-build-spike.md).

Headline: the existing hand-written build order is already a valid
topological order (0 violations across 1,279 extracted dependency edges, now
enforced by a structural preflight + two pinned tests), and splitting one
already-modularized group (`poly`, 21 of 148 fields) out of the shared struct
eliminates its hub footprint entirely — 0 lines touched in `complex.rs` for a
new declaration inside `poly.rs`, down from up to 3. Recommend applying level 1
(dependency table + structural preflight) to `creal.rs` without reservation;
recommend piloting the module-split (level Part B) on ONE already-separate
`creal/*.rs` file before generalizing, given the estimated ~9,000 call-site
churn across the full 441-field struct.

**WIP (agent-python-layer, 2026-08-24).** Strand
[`docs/python-2026-08/`](docs/python-2026-08/README.md). Plans 01-03 and the
quality goal (`10-quality-best-practices.md`) are complete on `main`. Q1-Q8
landed: property-based + Rust-side tests + a `ty` ratchet (Q1, which found a
replay that certified an empty assertion stack); the zero-copy audit and
`solve_smtlib_with_model` ending the double solve (Q2); release wheels with a
3.14t build and a smoke-install gate (Q3); the eight open tier-R rows (Q4);
typed stubs from the Rust signatures via pyo3-stub-gen at 96.9%, stubtest and
an `Any` ratchet (Q5); the CAS long tail -- ntheory / combinatorics / stats /
special / transforms / normal forms / moment provers / ansatz / gf / boolean /
algebraic, 179 items tested against sympy as oracle, three disagreements
argued and pinned (Q8, coverage 302 -> 471); panic-surface hardening -- a
probe took reachable panics 3 -> 0 and crashes 19 -> 2, the rest typed at the
boundary (Q7). Plus `axeyum.m` (Mathematica-shaped verbs) and a runnable
`python/examples/gallery.py`. Coverage `tier_r_unreferenced=0`.

Both prior follow-ups are now closed: the AGENT/knowledge fact-fixture drift
was refreshed (targets moved to `nat-modeq-symm/trans` and a nursery-derived
mobility count), and the deep-`Clone`/`Drop` segfault is guarded at the
boundary by a `MAX_EXPR_DEPTH` iterative-depth check that raises
`BudgetExceeded` (an iterative Clone in `axeyum-cas` remains the deeper fix).

Detail and older landed rows moved to [`../notes/python-layer.md`](docs/plan/notes/python-layer.md).

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

**Your lane's block (`DONE`, retrieval, 2026-08-27).** See the detail below.

**Track:** Refactor 2026-08-27 — the retrieval gate on marginal cost per theorem
**Phase:** ADR-0608 landed; tool in the tree, controls mutation-verified
**Date:** 2026-08-27

## Summary

Lanes repeatedly declared themselves blocked on a lemma that already existed,
proved, in the tree. Every existing instrument answers *"is this name taken?"*,
which cannot find a thing whose name you do not know.
`crates/axeyum-lean-kernel/examples/shape_search.rs` answers *"does a
declaration of this SHAPE exist, anywhere, under any name?"* over
`Kernel::environment()`, covering **every** declaration kind, and it
distinguishes a genuine zero from a query it was never pointed at.

## Delivered

- `crates/axeyum-lean-kernel/src/shape_index.rs` — the index and query engine.
  Indexes conclusion head, per-hypothesis head **taken under that hypothesis's
  own telescope**, type constants, opt-in value constants, and a canonical type
  shape for duplicate detection.
- `crates/axeyum-lean-kernel/src/shape_index/shape_index_tests.rs` — 19
  controls, each written so that deleting the guard it names turns it red.
- `crates/axeyum-lean-kernel/examples/shape_search.rs` — the CLI.
- `docs/research/09-decisions/adr-0608-…md` — the decision.
- Appendix to `docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`
  — the audit, the measurements, and the stated blind spots.

## Measured

| | |
|---|---|
| declarations indexed (`--include-constructed`) | 1,797 across 10 prelude groups |
| index build | ~13 s release; `--index-values` adds no measurable cost |
| unit tests | 19, 0.20 s |
| audited "already existed" instances, 2026-08-25 → 08-27 | **17** (reported: 13); 3 landed as real duplicates |
| theorem pairs stating the same proposition under two names | **6**, none previously reported |
| `CReal` names with `_` / internal capital / **both** | 315 / 200 / **114** |

## Next

- Wire `--expect 1` / `--expect-absent` `checker_command`s into facts whose
  evidence is a `Definition`; today those use
  `kernel_declaration_projection --require-declaration`, which is correct but
  requires knowing the exact name.
- Size the inline-step route described in the appendix (index `Kernel::infer`ed
  `Prop`-typed subterms of checked proof values) against the cheaper
  alternative: a lint for `Prop`-typed subterms reused three or more times.
- Decide whether the six duplicate theorem pairs are deduplicated or
  deliberately aliased, and record which.

**Done, s6-wire-real-ledger, 2026-08-30.** [ADR-0810](docs/research/09-decisions/adr-0810-wire-the-credit-transaction-into-the-real-fact-ledger.md)
records the full measurement. Follow-on to
[ADR-0785](docs/research/09-decisions/adr-0785-credit-transactions-two-phase-commit-with-a-crash-sweep-that-actually-crashes.md)
(`l0-s6-credit-transaction`), which built and verified the two-phase-commit
engine over a self-contained fixture ledger but deliberately did not wire it
into `artifacts/facts/`. Summary:

**The measured real write set differs from what ADR-0785's follow-on note
assumed.** That note named three targets ("the fact JSON, the settled pins
file, and the generated dashboards"). Instrumenting an actual flip found "the
generated dashboards" is not one thing: `gen-safety-matrix.py` and
`gen-product-health.py` are pure-Python/fast, but `gen-ledger-coverage.py`
invokes `cargo run --release -p axeyum-lean-kernel` (a multi-minute kernel
build/run, not a per-fact write), and `gen-product-health.py` -- despite being
fast -- reads unrelated global state (latest CI runtime receipt, autogenesis
operation/outcome artifacts, `justfile`/`check.sh` content) that has nothing
to do with any one fact. So the transaction covers three targets, all full
rebuilds:

1. `artifacts/facts/<id>.json`
2. `artifacts/ontology/settled-fact-statement-pins.json` (via
   `check-settled-fact-statements.py`'s own `rewrite()`, reused unmodified)
3. `artifacts/safety-matrix/safety-matrix.tsv` +
   `artifacts/safety-matrix/safety-matrix-summary.md` (via
   `gen-safety-matrix.py`'s own `classify`/`render_tsv`/`render_summary`/
   `run_controls`, reused unmodified)

`artifacts/ledger-coverage.json` and `artifacts/product-health-v1.json` /
`docs/plan/generated/product-health.md` are NOT covered, named explicitly.

**`scripts/validate-facts.py` has a ZERO-line diff from this lane.** The
wiring reuses its `validate_one(path, fact, known_ids)` directly via
`importlib`, gating every proposed fact before a transaction is proposed, and
never needed to touch the file the task said I "may edit."

Detail moved to [`../notes/s6-wire-real-ledger.md`](docs/plan/notes/s6-wire-real-ledger.md).

Lane: `safety-matrix-semantics`
Phase: S0 of the trusted-library safety roadmap (ADR-0717)
Decision: [ADR-0795](docs/research/09-decisions/adr-0795-the-safety-matrix-measures-per-fact-evidence-and-coverage-is-a-second-axis.md)

**Status:** COMPLETE — audited all nine S0 safety-matrix columns against every
centrally-run gate providing the same protection. Two defects found in opposite
directions; the overstating one is repaired, the understating one is a second
axis the census now reports separately. ADR-0795.

## The finding

Eight of the nine columns ask *"does this fact's own record exercise this
protection"*. They were read as *coverage*. `exact_statement` never asked that
question at all — it reads a ledger-wide manifest — so the census already mixed
the two axes without saying so.

| column | census | true coverage | direction |
|---|---:|---|---|
| `exact_statement` | 2121 | 2121 | correct, wrong axis (S1, ADR-0763) |
| `kernel_theorem` | 1467 | 1956 resolved by S2 | understates by design |
| `per_theorem_footprint` | 59 | 1956 (S2 `guard_forbidden_trust`) | understates by 1903 |
| `env_footprint` | 1863 | 1863 | correct |
| `circularity` | **38 → 14** | 1956 (S2 self + alias) | **OVERSTATED and understated** |
| `semantic_falsification` | 95 | **8 demonstrated** (S3) | **OVERSTATES by 87** |
| `mutation_control` | 15 | not a per-fact protection | mis-shaped |
| `independent_replay` | 8 | not measurable from a fact (S4, ADR-0760) | understates, unquantified |
| `coverage_bearing_checker` | 1443 | 1443 | correct |

**The overstatement is the one to read first.** 24 of `circularity`'s 38 rows
were credited by `kernel_declaration_projection`, which walks no closure —
its own module doc says the projection "must not be confused with a transitive
closure". Every one names a `definition`, which has no proof body to be
circular in, and the committed greps do not even constrain the footprint-size
field. Two further alternatives in the pattern matched **zero** commands.

## Landed changes

| commit | what |
|---|---|
| `0dd554239` | lane opened; premise on record before conclusions existed |
| `839c98204` | `circularity` 38 → 14; `exact_statement` moved to a coverage axis excluded from `protection_count`; the four uncredited gates named in the summary with what each must emit |
| `ba8426aa1` | `scripts/tests/test_safety_matrix.py` — 7 controls, 4 of them mutations the census could not previously fail on |
| this | ADR-0795, index, status |

## Verdict on S1's control repair

Detail moved to [`../notes/safety-matrix-semantics.md`](docs/plan/notes/safety-matrix-semantics.md).

**`DONE` (2026-08-27).** Brief: build the statement-only import mode ADR-0604
§2 names as the missing segment of "properly use axeyum", and answer whether
doc 292's 15 `Nat.Coprime` `TrustedDeclaration` refusals are essential or an
implementation artifact.

**Finding 0:** the mode itself (`import_statement_ndjson`,
`import_candidate_statement_ndjson`) already existed, added 2026-08-18
(`161adde83`). The missing piece was narrower: a typed bridge from a
completed statement import to the exact `artifacts/facts/` shape, with
`formal.statement` being the KERNEL's own rendering rather than
hand-transcribed surface syntax (which every currently-committed
`F-ml430-nat-coprime-*` fact uses today). Built that bridge:
`crates/axeyum-lean-import/src/statement_goal_record.rs`
(`build_statement_goal_record`) plus `examples/statement_goal_record.rs`
(worked-example CLI, prints a fact-schema-shaped JSON on success or a typed
decline on refusal, never writes under `artifacts/facts/`).

Detail moved to [`../notes/statement-import.md`](docs/plan/notes/statement-import.md).

### L0–L4 — Graph-directed trusted library programme (`TODO`, P0–P2)

Run the accepted [ADR-0717](docs/research/09-decisions/adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md)
programme in this order:

1. **L0, P0 — theorem credit:** exact statement and closure identity, forbidden
   trust/target checks, nonzero coverage, semantic controls, and independently
   graded replay for every changed settled fact. See the
   [safety roadmap](docs/plan/trusted-library-safety-roadmap-2026-08-30.md).
2. **L1, P1 — graph authority:** freeze the pinned source/extractor and emit
   complete, sealed declaration edge layers; proof/value edges remain forbidden
   producer input. See the [artifact](docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md)
   and [graph](docs/plan/graph-directed-library-roadmap-2026-08-30.md) roadmaps.
3. **L2, P1 — infrastructure frontier:** join exact Axeyum identities,
   representability, destinations, obstructions, producers, and provenance;
   expose every score component and preserve `fact-frontier.py` legality.
4. **L3, P2 — discovery pilots:** after L0–L2, run one substrate, one reusable
   producer, and one destination pilot with falsification before search and a
   frozen local-ready comparison. See the
   [efficiency roadmap](docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md).
5. **L4, P2 — Lean adapter:** complete artifact replay, then an elaborated-goal
   adapter whose result Lean checks. Source/elaboration features remain blocked
   until a preregistered population measures demand.

Each phase's roadmap exit is mandatory. Zero-yield pilots remain results; raw
degree never authorizes work; broad Lean-source compatibility is not an exit.

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
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; all 203 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
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
- **Graph rank is advisory until its authority is complete:** module degree,
  declaration centrality, curriculum mapping, and cost estimates remain visible
  components. They never bypass fact-frontier legality, held-out isolation,
  representability, or the theorem-credit safety contract.
- **Proof data does not leak into autonomous discovery:** upstream proof/value
  dependency edges may measure and sequence work but are physically excluded
  from proof-isolated producer inputs and autonomous credit.
- **Three parallel library lanes have different jobs:** prefer one shared
  substrate/definition lane, one reusable producer lane, and one destination
  theorem/evaluation lane. Each owns disjoint status, script, artifact, and test
  paths; one generated writer owns every aggregate key.

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
- Library artifact compatibility: [`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`](docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md)
- Graph-directed library construction: [`docs/plan/graph-directed-library-roadmap-2026-08-30.md`](docs/plan/graph-directed-library-roadmap-2026-08-30.md)
- Trusted theorem-credit safety: [`docs/plan/trusted-library-safety-roadmap-2026-08-30.md`](docs/plan/trusted-library-safety-roadmap-2026-08-30.md)
- Definition and discovery efficiency: [`docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md`](docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md)
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
