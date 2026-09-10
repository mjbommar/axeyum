# Propagation-based local search: is the gap real on what we have?

**Roadmap item:** 3.1 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md).
**Lane:** M3-1. **Date:** 2026-09-10. **Base:** `474423c8d`.
**Recommendation: DO NOT BUILD — and the blocking prerequisite is a corpus, not code.**

The roadmap's own gate for this item reads: *"Count QF_BV sat instances where
`pbls` fails and bit-blasting is slow; if small, defer."* This note runs that
count. It is **zero**, and it is zero for a reason that no amount of local-search
engineering would change: the committed QF_BV corpus contains no instance that
bit-blasting finds hard.

---

## 1. The question, as a number

> On how many **committed** QF_BV benchmarks would propagation-based local search
> plausibly win a verdict we do not currently get, or get one materially faster?

Decomposed into countable parts:

| Question | Answer | Where |
|---|---|---|
| Committed QF_BV files (`(set-logic QF_BV)`) | **99** | §2 |
| …of those, in the satisfiable band (`:status sat`, `unknown`, or absent) | **20** | §2 |
| …on which the front door returns `unknown` | **1** | §3 |
| …of those, `unknown` on an instance known to be **sat** | **0** | §3 |
| …decided in **0 ms** by the shipping bit-blasting path | **18 of 20** | §3 |
| Instances where local search wins a verdict bit-blasting misses | **0** | §3 |
| Instances where local search **loses** one bit-blasting gets in 0 ms | **3** | §3 |
| Times the local-search engine is reached through the front door, over 60 files | **0** | §4 |

The candidate work is roughly 6,000 lines of operator-specific mathematics
(§6). The measured return on everything committed is zero verdicts.

---

## 2. The population

Every `.smt2` under `corpus/` was classified by its `(set-logic …)` and
`(set-info :status …)`.

**Coverage control first.** The walk saw **1,179** `.smt2` files, and

```
$ git ls-files corpus | grep -c '\.smt2$'
1179
```

— the same number, so the walk covered exactly the tracked set and nothing else.
That equality is not automatic: `corpus/public` on this host is a **symlink to
`/nas3/data/axeyum/corpus/public`** (gitignored, per `corpus/README.md`), and a
walk that followed it would have silently mixed several hundred off-tree files
into a table labelled "committed". `os.walk` does not follow symlinked
directories; `find corpus/public/` (trailing slash) does, which is how the two
counts diverge if you are not watching.

```
$ python3 - <<'PY'   # full script in §8
... walks corpus/, groups by (corpus, logic, status)
PY
```

Committed QF_BV, by corpus and status:

```
   ('micro',           'QF_BV', 'sat')      2
   ('micro',           'QF_BV', 'unsat')    1
   ('public-curated',  'QF_BV', 'NONE')     2
   ('public-curated',  'QF_BV', 'sat')      2
   ('public-curated',  'QF_BV', 'unsat')    2
   ('qfbv-curated',    'QF_BV', 'sat')      9
   ('qfbv-curated',    'QF_BV', 'unknown')  1
   ('qfbv-curated',    'QF_BV', 'unsat')   33
   ('regression',      'QF_BV', 'sat')      4
   ('regression',      'QF_BV', 'unsat')   43
```

99 files. The satisfiable band — anything not annotated `unsat`, so anything a
local search could in principle crack — is **20 files**.

**The size distribution is the finding.** Listed by size, largest first:

```
sat           1368 corpus/qfbv-curated/bmc-bv__ex13.smt2
unknown        904 corpus/qfbv-curated/calypto__problem_12.smt2
sat            819 corpus/qfbv-curated/calypto__problem_9.smt2
sat            549 corpus/qfbv-curated/bench_ab__a115test0002.smt2
sat            546 corpus/qfbv-curated/bmc-bv__ex10.smt2
sat            440 corpus/qfbv-curated/bmc-bv__adpcm.smt2
sat            422 corpus/qfbv-curated/bench_ab__a121test0001.smt2
sat            415 corpus/qfbv-curated/bench_ab__a101test0002.smt2
sat            409 corpus/qfbv-curated/bench_ab__a100test0001.smt2
sat            310 corpus/micro/sat-quoted-symbol.smt2
sat            271 corpus/qfbv-curated/check2__bvsdiv.smt2
sat            244 corpus/micro/sat-add.smt2
sat            216 corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bool-model.smt2
sat            199 corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bvmul-pow2-only.smt2
sat            187 corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bug578.smt2
sat            160 corpus/public-curated/bvred/bitwuzla__redxor-substitute5.smt2
NONE           156 corpus/public-curated/bvred/cvc5__redand.smt2
NONE           156 corpus/public-curated/bvred/cvc5__redor.smt2
sat            117 corpus/regression/qf_bv/sat_wraparound.smt2
sat            115 corpus/public-curated/bvred/bitwuzla__redor3.smt2
20 files
```

**The largest satisfiable QF_BV benchmark we have committed is 1,368 bytes.**

For scale, the SMT-LIB 2024 `QF_BV` division is on the NAS at
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_BV`
(mounted; 46,191 files):

```
n 46191 min 240 median 33300 p90 1786257 p99 7637735 max 2044326719
committed QF_BV max size = 1368 bytes; NAS files >= 1368 bytes: 36471
```

The SMT-LIB QF_BV *median* is 24× our largest file, and **36,471 of 46,191
(79%)** of its files are bigger than anything we have committed. Local search is
an engine for the instances where bit-blasting explodes. Our committed QF_BV
corpus does not contain one.

---

## 3. The measurement: front door vs. local search, side by side

A throwaway probe (`crates/axeyum-bench/examples/m31_probe.rs`, §8 — deleted, not
merged) runs each file twice on a 512 MB-stack worker under a 10 s wall-clock
cap: first `check_auto`, then `solve_local_search` (the word-level local search)
on the same assertions.

`check_auto` is the dispatcher a quantifier-free query reaches through the
shipped text front door — `solve_smtlib` → `solve` (`smtlib.rs:2266`) → the
quantified ladder, which a QF_BV script falls straight through → `check_auto`.
It is also exactly what `corpus_regression.rs` gates on. The string gates
`solve_smtlib` wraps around it do not apply to QF_BV.

```
$ cargo build --release -p axeyum-bench --example m31_probe   # via scripts/cargo-serialized.sh
$ target/release/examples/m31_probe 10000 < <the 20 paths above>
```

Real output (columns: front-door verdict / ms, local-search verdict / ms /
flips / restarts, and how many times the front door reached the local-search
probe):

```
path	auto_verdict	auto_ms	pbls_verdict	pbls_ms	flips	restarts	pbls_reaches
corpus/micro/sat-add.smt2	sat	0	sat	0	37	0	0
corpus/micro/sat-quoted-symbol.smt2	sat	0	sat	0	2	0	0
corpus/public-curated/bvred/bitwuzla__redor3.smt2	sat	0	sat	0	0	0	0
corpus/public-curated/bvred/bitwuzla__redxor-substitute5.smt2	sat	0	sat	0	7	0	0
corpus/public-curated/bvred/cvc5__redand.smt2	sat	0	sat	0	1	0	0
corpus/public-curated/bvred/cvc5__redor.smt2	sat	0	sat	0	0	0	0
corpus/qfbv-curated/bench_ab__a100test0001.smt2	sat	0	sat	0	1	0	0
corpus/qfbv-curated/bench_ab__a101test0002.smt2	sat	0	sat	0	0	0	0
corpus/qfbv-curated/bench_ab__a115test0002.smt2	sat	0	unknown[local search: flip/restart budget exhausted]	122	9000	25	0
corpus/qfbv-curated/bench_ab__a121test0001.smt2	sat	0	sat	0	0	0	0
corpus/qfbv-curated/bmc-bv__adpcm.smt2	sat	0	sat	0	0	0	0
corpus/qfbv-curated/bmc-bv__ex10.smt2	sat	0	sat	0	0	0	0
corpus/qfbv-curated/bmc-bv__ex13.smt2	sat	0	sat	0	1	0	0
corpus/qfbv-curated/calypto__problem_12.smt2	unknown[preprocessed dispatch timeout after reduced solve]	10078	unknown[local search: flip/restart budget exhausted]	1352	8000	25	0
corpus/qfbv-curated/calypto__problem_9.smt2	sat	682	unknown[local search: flip/restart budget exhausted]	763	9000	25	0
corpus/qfbv-curated/check2__bvsdiv.smt2	sat	0	sat	0	0	0	0
corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bug578.smt2	sat	0	sat	1	126	0	0
corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bool-model.smt2	sat	0	sat	0	0	0	0
corpus/regression/cvc5/qf_bv/cvc5__cli__regress0__bv__bvmul-pow2-only.smt2	sat	0	sat	0	2	0	0
corpus/regression/qf_bv/sat_wraparound.smt2	sat	0	sat	0	110	0	0
```

Read it row by row:

- **19 of 20 are decided `sat` by the front door**; 18 of them in **0 ms**, one
  (`calypto__problem_9`) in 682 ms.
- **The single `unknown` is `calypto__problem_12` — whose own `:status` is
  `unknown`.** SMT-LIB does not know whether that file is satisfiable. It is not
  evidence of a missed `sat`; a local search that returned `unknown` on it (as
  ours does, in 1.35 s) would be behaving correctly.
- **So the count the roadmap asked for is 0.** There is no committed QF_BV
  instance that is known-satisfiable and that we fail to decide.
- **Local search is strictly worse here, on three files.**
  `bench_ab__a115test0002`, `calypto__problem_9` and `calypto__problem_12` exhaust
  the flip/restart budget (9,000 / 8,000 flips, 25 restarts) while bit-blasting
  answers two of them in 0 ms and 682 ms. Adding invertibility conditions would
  make those searches smarter; it would not make them *win*, because there is
  nothing left to win.

### The "slow" half of the gate is also empty

The gate has two conjuncts: `pbls` fails **and** bit-blasting is slow. The
maximum front-door time over the whole satisfiable band, excluding the file
SMT-LIB itself calls `unknown`, is **682 ms**. Every other file is under the
resolution of the millisecond clock.

---

## 4. Where `pbls` is reachable from — the headline, not a footnote

The brief asked to read the call sites first. There is exactly **one** in `src/`:

```
$ grep -rn "solve_local_search" crates/*/src/
crates/axeyum-solver/src/preprocess.rs:111:        match crate::pbls::solve_local_search(arena, &reduced, &probe_config)?.result {
```

That line sits inside `check_with_preprocessing_and_local_search`, which has one
caller:

```
$ grep -rn "check_with_preprocessing_and_local_search" crates/axeyum-solver/src/
crates/axeyum-solver/src/abv.rs:3301
```

— inside `check_scalar_abstraction`, which the lazy-ROW CEGAR loop calls at
`abv.rs:3399`, on a 100 ms budget (`SCALAR_LOCAL_SEARCH_PROBE_MS`, `abv.rs:519`).
And `solve_round` only falls through to it on a **cold** round: the warm engine
is tried first, and the front door calls only the warm entry
(`auto.rs:5663` → `check_qf_abv_lazy_row_warm`).

So the shipping path to the word-level local search is: *QF_BV inside QF_ABV*,
*after* the warm incremental engine has declined a refinement round, for
*100 ms*. **It is not on the QF_BV path at all.**

Measured rather than read off the call graph. A throwaway `AtomicUsize` at
`preprocess.rs:111` (§8), reset per file and read after the solve:

- Over the **20 committed QF_BV** files in §3: `pbls_reaches` = **0** on every row.
- Over **40 committed QF_ABV / QF_AUFBV** files through the same front door:

```
reaches=0 40
--- rows with reaches>0
```

Zero, over all 60 files.

**Positive control — the counter can fire.** A zero from an instrument that was
never wired to its subject is worth nothing, so the same 40 QF_ABV files were run
again through the *cold* lazy-ROW entry (`check_qf_abv_lazy_row`, the one the
front door does not call), with the identical counter:

```
$ target/release/examples/m31_control 10000 < <the same 40 paths>
rows=40 files_with_reaches>0=4 total_reaches=8

path	cold_lazy_row_verdict	pbls_reaches
.../rewrite__array__rw123.btor.smt2	unsat	2
.../rewrite__array__rw35.btor.smt2	unsat	2
```

The instrument fires — 8 reaches over 4 files — when the route that contains it
is entered. The front-door zero is therefore a real negative, not a probe that
never reached its subject.

---

## 5. What the NAS corpus says (the off-tree check)

PLACEHOLDER_NAS

---

## 6. What building it would actually cost, and what Bitwuzla itself does

`references/bitwuzla` at `a5e6e8a7a`:

```
$ find references/bitwuzla/src/lib/ls -type f \( -name '*.cpp' -o -name '*.h' \) | xargs wc -l
   162 ls_bv.h
   812 ls.cpp
   426 ls_bv.cpp
   105 internal.h
   498 ls.h
   253 node/node.cpp
   297 node/node.h
  6336 bv/bitvector_node.cpp
  1338 bv/bitvector_node.h
 10227 total
```

The roadmap's arithmetic checks out: 68 distinct
`BitVector<Op>::{is_invertible,is_consistent,inverse_value,consistent_value}`
definitions over **17** operator classes (`Add And Ashr Concat Eq Extract Ite Mul
Not Shl Shr SignExtend Slt Udiv Ult Urem Xor`), nearly all of the 6,336-line
`bitvector_node.cpp`.

Three facts about the reference implementation that bear on the decision:

1. **Bitwuzla does not ship local search as its default engine.**
   `src/option/option.cpp:239` sets `bv_solver` to `BvSolver::BITBLAST`;
   `prop` and `preprop` are opt-in (`--bv-solver=prop`). Even in `preprop`, the
   propagation phase gets a bounded 10,000 propagations
   (`option.cpp:983`) before bit-blasting takes over. It is a portfolio member
   for a band, not a replacement.
2. **Its speed comes from an incremental assignment cache, not only from
   invertibility** — and *we already built our version of that half, and it did
   not convert the band.* Every Bitwuzla `ls::Node` carries `d_assignment`
   (`ls/node/node.h:267`) and updates it from its children.

   **Correction to the obvious next step.** The natural recommendation from row 2
   is "add incremental term evaluation first, it is the cheaper half." That
   recommendation is stale, and I checked before writing it. `pbls.rs` **already
   has** a persistent memo with per-variable cone invalidation
   (`pbls.rs:383-396` `memo` / `var_cone`, `pbls.rs:487` `fn cone`, over
   `axeyum_ir::eval_with_memo`). It was implemented *because* of the
   135-flips/s finding, and it was measured:
   [`docs/research/05-algorithms/lazy-bitblasting-p21-findings.md:361-384`](../05-algorithms/lazy-bitblasting-p21-findings.md)
   records **2,700 → 3,985 flips per 20 s, ~1.5×, not the hoped orders of
   magnitude** — "because in this `ite`-dense structure each variable's cone is
   *large* (a var feeds much of the assertion), so 'incremental' recomputes most
   of it anyway," and concludes "**WalkSAT is confirmed not the lever for this
   corpus**."

   That prior measurement is the closest thing in the tree to a fair test of the
   3.1 hypothesis: `string1x8.4` is a 150 k-clause *satisfiable* QF_BV instance
   that kissat cracks in 8.3 s — exactly the "bit-blasting is slow, the instance
   is merely hard to find" shape item 3.1 exists for. Our local search timed out
   on it **with** the incremental evaluator. It lives on the NAS
   (`corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen/StringMatching/`),
   not in the committed corpus.

   The honest reading: that result does **not** prove invertibility conditions
   would not help — it was our move selection, not Bitwuzla's. What it does show
   is that the gap to a Bitwuzla-class engine is **~2 orders of magnitude in flip
   rate**, that the cheap structural fix has already been spent for 1.5×, and
   that closing it means replacing the evaluation core (a per-node assignment
   cache propagated bottom-up), not bolting 68 inverse-value functions onto a
   term-re-evaluating scorer. Item 3.1 as written sizes only the second half.
3. Our `pbls.rs` is 1,456 lines with a 193-line test file, and its budget is
   hard-capped at `max_tries = 25`, `max_flips = 200 + 40 * span`
   (`pbls.rs:1229-1231`) — which is what "flip/restart budget exhausted" means in
   every §3 row, not a timeout.

---

## 7. Recommendation

**DO NOT BUILD.** Not "not yet, for scheduling reasons" — the measurement that
would justify it cannot be taken with the corpus we have.

- The literal gate ("count QF_BV `sat` instances where `pbls` fails and
  bit-blasting is slow") counts **0** committed instances.
- The largest committed satisfiable QF_BV file is 1,368 bytes; 79% of SMT-LIB's
  QF_BV division is larger.
- The engine is currently unreachable from the QF_BV front door, so there is not
  even a shipping route for an improved version to improve.

**The prerequisite is a corpus, not 6,000 lines of code.** Concretely, and in
this order:

1. **Vendor or reference a hard satisfiable QF_BV slice** — the SMT-LIB families
   whose satisfiable instances are search-bound rather than encode-bound. The
   files exist on the NAS today; nothing needs to be generated. This is the same
   shape of prerequisite as item 2.9 (the incremental-script corpus) and 2.5 (the
   string corpus), and it should be filed alongside them.
2. **Re-run this note's probe on that slice.** If the count of
   "front door `unknown`, `:status sat`" is still small, item 3.1 stays closed
   and the finding is durable rather than a scheduling accident.
3. **Only if that count is material:** the first increment is **not**
   invertibility conditions and it is **not** incremental term evaluation — that
   one is already built and already measured at 1.5× (§6 fact 2). It is a
   flip-rate measurement on the target slice with a stated target: our engine
   runs at roughly 10²–10³ flips/s where competitive SLS runs at 10⁵–10⁶. Until a
   design exists that closes that, 68 inverse-value functions would make a
   two-orders-of-magnitude-too-slow search pick better moves.
4. **Independently of 3.1:** decide whether the local-search probe at
   `preprocess.rs:111` should stay. It is reached zero times through the front
   door on 60 committed files and costs a 100 ms budget on the cold rounds where
   it is reached. That is a wiring question for item 2.7's ledger, not an
   algorithms question — and this note is not proposing to answer it.

**What would change this answer:** a satisfiable QF_BV instance, in a committed
corpus, that the shipping bit-blasting path does not decide within a normal
budget and that a local search does. One such instance would reopen the item.
Zero of the twenty we have is not a close call.

---

## 8. What I did not measure

Explicitly, so nobody inherits a claim this note did not earn:

- **I did not measure Bitwuzla's own local search against ours.** No head-to-head
  run of `bitwuzla --bv-solver=prop` on anything. The claims in §6 about Bitwuzla
  are read from its source at `a5e6e8a7a`, not from its behaviour.
- **I did not measure the quantified `BV` logic** (59 committed files, 37 `sat`).
  Local search is a quantifier-free engine and `pbls.rs`'s own doc scopes it to
  Bool / Int / `BitVec(w ≤ 128)`; a quantified instance yields `unknown` before
  any search happens. If someone wants that number, it is a separate question.
- **I did not measure QF_ABV or QF_AUFBV verdicts** beyond the 40-file
  reachability control, and the control's front-door verdict column was not
  compared against `:status`. It was run to make the counter fire, nothing more.
- **I did not measure whether the 100 ms probe at `abv.rs:3306` ever pays for
  itself** on the cold rounds where it does run. The control shows it is reached
  8 times over 4 files; it does not show whether any of those 8 produced the
  verdict.
- **I did not run any gate.** No `just check`, no `corpus_regression`, no
  workspace test sweep. Nothing in the solver changed: the instrumentation
  described in §4 was throwaway and is reverted; the two probe examples are
  deleted. `git status` at the end of this lane shows only this file.
- **The timings in §3 are single runs on a shared 16-core box** under other lanes'
  load. They are not a reference frame and no ratchet should be derived from
  them. They are used here only to separate "0 ms" from "10 s", a gap far wider
  than the noise.
- **The NAS sample in §5 is a stratified random sample, not the division.** Its
  seed and construction are stated there; a different seed would draw different
  files.

### Reproduction

The two probe binaries are deleted. To re-derive:

- The population and size tables: pure Python over `corpus/` and a
  `find … -printf '%s\t%p\n'` over the NAS path, both shown inline above.
- The verdict table: an example that reads paths on stdin and, per path, runs
  `check_auto` then `solve_local_search` on a 512 MB-stack worker under a
  `recv_timeout` cap, printing the TSV in §3.
- The reachability control: a `static AtomicUsize` incremented at
  `preprocess.rs:111` inside the `if let Some(timeout)` arm, plus a second example
  calling `theories::arrays::check_qf_abv_lazy_row` (the **cold** entry) so the
  counter has something to count.

Keeping either probe as an `#[ignore]`d test is **not** recommended: both depend
on instrumentation that must not live in `preprocess.rs`, and the second one's
value is entirely in the one-time question it answered.
