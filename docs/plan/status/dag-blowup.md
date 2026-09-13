# Lane: dag-blowup — a depth cap bounds path length, a worklist bounds stack, neither bounds path count

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, dag-blowup, 2026-09-12).**

**Task.** One confirmed exponential term walker (`auto::lin_form`), then triage
the population: a scan had found ~136 branching `TermId` walkers with no memo,
and the standing instruction was to treat that as a lead generator, not a bug
count.

**Outcome.** **Seventeen** walkers memoised across ten modules. The repro that
took 10.41 s at depth 26 and `unknown` at 27 now decides depth 40 in **0.01 s**
(z3 0.04 s, cvc5 0.03 s), and **26 of 28** operator-class repro families are flat to
depth 32 — the shipped binary re-swept end to end, not inferred. The shape is written up as
[ADR-1940](../../research/09-decisions/adr-1940-a-depth-cap-bounds-path-length-a-worklist-bounds-stack-neither-bounds-path-count.md).
**No division moved.** On the corpora we measure this is **robustness, not board
points**, and the measurement that says so is below.

## The generalizable finding

Four standard, locally correct defences were in place across these sites and
**none of them defends against this**:

| defence | what it bounds | sites carrying it |
|---|---|---|
| `depth > 256` / `depth > 1024` | path LENGTH | `lin_form`, `interval_of`, `affine_in`, `accumulate_max_abs` |
| explicit worklist (recursion removed) | STACK | `lra::IntCollector::linearize`, `dl_online::ScanState::linear`, `lia_online::IntRowBuilder::linearize` |
| step counter + deadline | WALL CLOCK, after the fact | `dl_online::ScanState::linear` |
| a `HashMap` cache on the LEAVES | leaf re-materialisation | `abv::RowCtx::memo`, `qinst_egraph::collect_vars`'s `seen` |

The cost is path COUNT. At sharing depth 30 all `2^30` calls sit at depth ≤ 30,
the worklist holds `2^30` shallow items, and the deadline reports the burn
instead of preventing it. Two of the worklist sites carry a comment headed *"Why
this is an explicit worklist and not native recursion"* citing the stack
overflow it fixed — true, and exactly what makes the function read as already
handled. The leaf caches read the same way: a `HashMap` in the walk that is
keyed on the wrong thing.

**Fixing most of them is not fixing it.** Four of the seven instances on the
QF_LIA route removed the cliff by ONE level, because the cost is a product of
doubling factors.

## Landed

| SHA | what |
|---|---|
| `20967ee96` | `auto::{lin_form, interval_of, affine_in, accumulate_max_abs}` + the expansion-count guard |
| `a974c2348` | `lra::{Collector,IntCollector}::linearize`, `dl_online::ScanState::linear` + the depth-40 verdict guard |
| `7cb53fc6a` | `nra_real_root::{collect,collect_int,collect_multi}`, `bv2nat_blast::linear_form`, `quant_fourier_motzkin::affine`, `lia_online::IntRowBuilder::linearize` |
| `ba59ecbe4` | ADR-1940, this file, generated PLAN/index |
| `b1a852035` | the four triage instruments in `scripts/` |
| `f38e24a3d` | `dl_online`: check the operand count instead of letting `split_off` panic |
| `3dfc49d16` | the count guard retargeted so its mutation dies in 7.5 s, not in hours |
| `1fe1201f3` | `abv::RowCtx::{abstract_term, abstract_with_array_eq}`, `pbls::unit_affine_const`, `qinst_egraph::collect_vars` — **and a correction** |

## The repro, and what each round bought

`(let ((v0 (+ x 1))) (let ((v1 (+ v0 v0))) … (<= v_d 100)))` — `d + 2` arena
nodes, `2^(d+1)` root-to-leaf paths. Release, one pinned core.

| depth | 24 | 25 | 26 | 27 | 30 | 36 | 40 |
|---|---|---|---|---|---|---|---|
| shipped `main` | 2.61 s | 5.13 s | 10.41 s | unknown | unknown | unknown | unknown |
| + `auto.rs` (4 of the route's 7) | 0.28 s | 0.55 s | 1.07 s | 2.13 s | 7.51 s | 18.0 s | 18.0 s |
| + `lra`, `dl_online` (all 7) | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s |
| z3 4.13.3 | — | — | 0.04 s | 0.05 s | 0.05 s | — | 0.04 s |
| cvc5 1.3.4 | — | — | 0.04 s | 0.04 s | 0.03 s | — | 0.03 s |

The flat 18.01 s row is not a plateau, it is `dl_probe_budget(24 s)` to the
hundredth: `dl_online::ScanState::linear` was burning the DL probe's whole slice
and the next route then decided instantly.

## Triage: measured, not read

A source scan is a lead generator, and this one's blind spots were expensive.
The first version counted free-function self-recursion only and **missed both
instances that dominated the profile** — one is a method (`self.linearize(`),
the other is not recursive at all. Three blind spots, all demonstrated:

1. `self.name(` method recursion (the scan excluded a dot-preceded call).
2. An explicit worklist — no self-call at all.
3. A recursion inside `for arg in args { … }` — one textual call site that
   branches at runtime (`accumulate_max_abs` is this, and no version of the scan
   lists it).

So the instrument is a **repro family** (`scripts/dag-blowup-repro-family.py`):
one `let`-doubling chain per operator class, 28 families over 13 logics, each
swept to the depth where it stops being flat
(`scripts/dag-blowup-family-sweep.py`), with `perf` on every family that
doubled. A family that doubles NAMES a live instance; `perf` names the function.

| family | division | shipped `main` | now | dominant symbol |
|---|---|---|---|---|
| `int_add` | QF_LIA | ×2.7/level from d21 | flat to d32 | `auto::lin_form` |
| `int_sub` | QF_LIA | ×3.0/level from d14 | flat to d32 | `auto::lin_form` |
| `eq_chain` | QF_LIA | ×1.8/level from d22 | flat to d32 | `auto::affine_in` |
| `idl` | QF_IDL | ×1.8/level from d21 | flat to d32 | `dl_online::ScanState::linear` |
| `real_add` | QF_LRA | ×2.0/level from d25 | flat to d32 | `lra::Collector::linearize` |
| `nra_add` | QF_NRA | ×1.9/level from d20 | flat to d32 | `nra_real_root::collect` 9.7% |
| `nia_add` | QF_NIA | ×1.4/level from d21 | flat to d32 | `nra_real_root::collect` 27.5% |
| `str_len` | QF_SLIA | ×1.8/level from d22 | flat to d32 | `bv2nat_blast::linear_form` 11.1% |
| `array_sel` | QF_ALIA | ×1.9/level from d20 | flat to d32 | `abv::…::abstract_with_array_eq`, then `pbls::unit_affine_const` **99.6%** |
| `bool_and` | QF_UF | ×2.0/level from d26 | **still doubles** | `term_walk::collect_top_binary_conjuncts` 61.8% |
| `quant_lia` | LIA | ×2.0/level from d19 | ×2.0 from d23 (2 levels bought) | `qinst_egraph::collect_app_candidates` 18.9% + 68% allocator |
| 17 other families | — | flat | flat | — |

Final sweep of all 28 on the shipped binary: **26 flat to depth 32**, `bool_and`
×1.99 and `quant_lia` ×1.98. Those two are the whole remaining doubling surface.

### A claim of mine that was false, and the measurement that caught it

`7cb53fc6a` reported `abv::RowCtx::abstract_with_array_eq` as producing output
that is itself exponential, therefore "no memo can fix this". **That was wrong
and I wrote it without reading the function.** It is a plain structural rebuild
over an interning arena, so the output is a DAG of the same size and the
exponential is the walk. Memoised, `array_sel` went from 4.60 s at depth 30 and
doubling to **0.13 s flat to depth 32**. The discriminator is cheap and is now
in the ADR: does the function RETURN a rebuilt term (memoisable), or PUSH one
entry per leaf reached into a flat list (not)?

### The two that genuinely are not memo bugs

- **`term_walk::collect_top_binary_conjuncts`** — its contract says it
  *"deliberately preserves duplicates"*, so `(and v v)` over a depth-29 shared
  DAG genuinely has `2^30` leaves.
- **`qinst_egraph::collect_app_candidates`** — pushes one `(term, indices)` per
  PATH, so the same trigger candidate appears many times in `out`.

A visited set dedupes both OUTPUTS, which changes what the consumer sees: a
Boolean-structure route with eleven call sites carrying "extra leaf semantics",
and a quantifier-trigger route. That is a contract decision wanting its own
evidence, not a drive-by cache. **These two are the next task**, and they are
the whole remaining doubling surface in 28 families.

### Census

Token-based, approximate in both directions, reported as a lead generator
(`scripts/dag-blowup-walker-census.py`).

| | branching `TermId` walkers | no memo token | with a depth cap |
|---|---:|---:|---:|
| base `a25e98639` | 216 | **164** | 5 |
| after this lane | 207 | 152 | 2 |

164 is not 164 bugs and was never quoted as one.

## Real-corpus reachability: narrow, and the fix is priced accordingly

Deep `let` nesting is common; this blowup needs each level referenced at least
**twice** along one spine. Measured with `scripts/dag-blowup-share-paths.py`,
which computes the exact quantity governing the walk.

| population | files scanned | `let` depth ≥ 25 | `+ - *` paths ≥ 2^20 | max |
|---|---:|---:|---:|---:|
| QF_LIA, whole division | 12,422 of 13,306 | 3,448 | **0** | 39,800 |
| QF_LIA board slice | 200 | 55 | **0** | 128 |
| QF_UFLRA board slice | 197 | 112 | **0** | 36 |
| QF_NRA board slice | 200 | 46 | **0** | 158,100 |
| QF_NIA / QF_SLIA / QF_UF / QF_UFLIA / QF_IDL slices | 997 | 56 | **0** | ≤ 374 |

Over `and`/`or` spines the picture is the same except for one family: QF_IDL's
`Averest` sorting benchmarks, where `BubbleSort_safe_blmc016.smt2` carries
**8,394,292** and/or paths in 1.4 MB of source — genuine sharing amplification,
not size. Both arms decide it `unsat` in 3.6 s, so even there it is not a cliff.

Two caveats on the metric, because the number misleads without them.
`max_paths` equals the LEAF COUNT for an unshared spine, so a large value alone
is not blowup — blowup is paths ≫ nodes, and the QF_NRA 158,100 and QF_LIA
39,800 rows are wide flat sums. And the analyser saw 12,422 of QF_LIA's 13,306
files: 47 exceeded its own 20 s per-file budget (it is itself a branching walk)
and the rest were oversized. It reports them rather than dropping them.

So: **robustness, not board points.** It removes a cliff a competition generator
or an adversarial input reaches trivially and that today's public corpora do not.

## Verification

**Interleaved per-file A/B**, both arms back to back on one pinned core per
worker, arm order alternating by file index, 24 s budget, 4 workers, shipped
`main` (arm A) vs this lane (arm B). 200 files per division.

| division | raw gains / losses / flips | wall delta | re-checked |
|---|---|---:|---|
| QF_LIA | 0 / 2 / 0 | +1.2% | **0 / 0 / 0** |
| QF_UFLRA | 1 / 2 / 0 | +2.7% | **0 / 0 / 0** |
| QF_LRA | 1 / 2 / 0 | +0.2% | **0 / 0 / 0** |
| QF_UF (control) | 0 / 0 / 0 | +0.3% | — |

**Every raw gain and loss was noise, and the re-check says so.** Each of the
eight was re-run at 4 interleaved repetitions on a quiet pinned core: all decide
identically in BOTH arms, at 2.5–18.4 s against a 24 s budget. That is the
near-budget class the brief warned about, and it is worth recording as a
property of the harness: at a 24 s budget with 4 concurrent workers, roughly
1–1.5% of files flip on ambient load alone. A single-pairing gain or loss in
that band is not evidence.

Zero `sat`↔`unsat` flips anywhere, raw or re-checked.

**Gates**, every one with its result line and count read, not its exit status:

- Five z3 differential fuzzes, `--features z3`, nonzero counts confirmed:
  `qf_lra` 5, `simplex_lra_fallback` 1, `qf_uflra` 1, `difference_logic` 4,
  `qf_lia` 4 — **15 tests, 0 failures**. Plus `abv_differential_fuzz` 1, 0
  failures.
- Solver lib sweep `--features full -- --test-threads=4`: **1722 passed, 0
  failed**, run after each of the three code batches.
- `corpus_regression` 2 passed; `progress_frontier --features full
  --test-threads=1` **12 passed, 0 failed** (its artifacts were NOT comparable
  on a load-9 box, so they were reverted rather than committed).
- String route: `online_string_front_door` 48, `word_first_fallback` 13,
  `qf_slia_fixed_splice` 82, `stoi_len_abstraction` 13 — 0 failures.
- Array route: `abv_lazy_ext` 10, `abv_lazy_row` 5, `arrays` 9,
  `array_valued_uf_online` 2, `array_scenarios` 1 — 0 failures.
- Clippy `-p axeyum-solver --all-targets --features full -- -D warnings`: clean.
  `cargo fmt --all --check`: clean. `check-merge-hygiene.sh` PASS,
  `check-suite-gating.py` PASS.

## Guards added, and one of them was rewritten because it did not work

- `lin_form_expands_a_shared_dag_once_per_node` — asserts the memo's EXPANSION
  COUNT, not a wall time. **Mutation-verified, and the first version failed that
  verification.** It was written at depth 30, which is `2^31` calls for the
  mutation it exists to catch; deleting the memo lookup did not fail it, it ran
  for ten minutes until killed. A guard that can only fire after an hour is a
  timeout. At depth 22 the same mutation fails it in **7.54 s** with `expanded
  16777215 nodes for a 25-node DAG` against a bound of 64.
- `shared_let_chain_of_depth_40_is_decided` — the front door, asserting `sat`.
  `2^41` paths; it does not return on the unmemoised tree. Deliberately the
  opposite depth choice to the guard above.

Both live in `auto.rs`'s inline test module, so they run under the existing
`-p axeyum-solver --lib --features full` pre-push gate and add no new suite for
`scripts/check-suite-gating.py` to require.

<!-- /plan-section -->
