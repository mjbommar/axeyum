# Lane: dag-blowup — a depth cap bounds path length, a worklist bounds stack, neither bounds path count

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, dag-blowup, 2026-09-12).**

**Task.** One confirmed exponential term walker (`auto::lin_form`), then triage
the population: a scan had found ~136 branching `TermId` walkers with no memo,
and the standing instruction was to treat that as a lead generator, not a bug
count.

**Outcome.** Eleven walkers memoised across seven modules, the repro that took
10.41 s at depth 26 and `unknown` at 27 now decides depth 40 in **0.01 s**
(z3 0.04 s, cvc5 0.03 s), and the shape is written up as
[ADR-1940](../../research/09-decisions/adr-1940-a-depth-cap-bounds-path-length-a-worklist-bounds-stack-neither-bounds-path-count.md).
No division moved: on the corpora we measure this is **robustness, not board
points**, and the measurement that says so is below.

## The generalizable finding

Three standard, locally correct defences were in place across these sites and
**none of them is a defence against this**:

| defence | what it bounds | sites carrying it |
|---|---|---|
| `depth > 256` / `depth > 1024` | path LENGTH | `lin_form`, `interval_of`, `affine_in`, `accumulate_max_abs` |
| explicit worklist (recursion removed) | STACK | `lra::IntCollector::linearize`, `dl_online::ScanState::linear`, `lia_online::IntRowBuilder::linearize` |
| step counter + deadline | WALL CLOCK, after the fact | `dl_online::ScanState::linear` |

The cost is path COUNT. At sharing depth 30 all `2^30` calls sit at depth ≤ 30,
the worklist holds `2^30` shallow items, and the deadline reports the burn
instead of preventing it. Two of the worklist sites carry a comment headed *"Why
this is an explicit worklist and not native recursion"* citing the stack
overflow it fixed — true, and exactly what makes the function read as already
handled.

**Fixing most of them is not fixing it.** Four of the seven instances on the
QF_LIA route removed the cliff by ONE level, because the cost is a product of
doubling factors.

## Landed

| SHA | what |
|---|---|
| `20967ee96` | `auto::{lin_form, interval_of, affine_in, accumulate_max_abs}` + the expansion-count guard |
| `a974c2348` | `lra::{Collector,IntCollector}::linearize`, `dl_online::ScanState::linear` + the depth-40 verdict guard |
| `7cb53fc6a` | `nra_real_root::{collect,collect_int,collect_multi}`, `bv2nat_blast::linear_form`, `quant_fourier_motzkin::affine`, `lia_online::IntRowBuilder::linearize` |

## The repro, and what each round bought

`(let ((v0 (+ x 1))) (let ((v1 (+ v0 v0))) … (<= v_d 100)))` — `d + 2` arena
nodes, `2^(d+1)` root-to-leaf paths. Release, one pinned core.

| depth | 24 | 25 | 26 | 27 | 30 | 36 | 40 |
|---|---|---|---|---|---|---|---|
| shipped `main` | 2.61 s | 5.13 s | 10.41 s | unknown | unknown | unknown | unknown |
| + `auto.rs` (4 of 11) | 0.28 s | 0.55 s | 1.07 s | 2.13 s | 7.51 s | 18.0 s | 18.0 s |
| + `lra`, `dl_online` (7 of 11) | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s |
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

So the instrument is a **repro family**: one `let`-doubling chain per operator
class, 28 families over 13 logics, each swept to the depth where it stops being
flat, with `perf` on every family that doubled. A family that doubles NAMES a
live instance; `perf` names the function.

| family | division | shipped `main` | this lane | dominant symbol |
|---|---|---|---|---|
| `int_add` | QF_LIA | x2.7/level from d21 | flat to d32 | `auto::lin_form` |
| `int_sub` | QF_LIA | x3.0/level from d14 | flat to d32 | `auto::lin_form` |
| `eq_chain` | QF_LIA | x1.8/level from d22 | flat to d32 | `auto::affine_in` |
| `idl` | QF_IDL | x1.8/level from d21 | flat to d32 | `dl_online::ScanState::linear` |
| `real_add` | QF_LRA | x2.0/level from d25 | flat to d32 | `lra::Collector::linearize` |
| `nra_add` | QF_NRA | x1.9/level from d20 | flat to d32 | `nra_real_root::collect` 9.7% |
| `nia_add` | QF_NIA | x1.4/level from d21 | flat to d32 | `nra_real_root::collect` 27.5% |
| `str_len` | QF_SLIA | x1.8/level from d22 | flat to d32 | `bv2nat_blast::linear_form` 11.1% |
| `quant_lia` | LIA | x2.0/level from d19 | one level, still doubles | `lia_online::…::linearize` 17.9%, `quant_fourier_motzkin::affine` 10.5% |
| `bool_and` | QF_UF | x2.0/level from d26 | unchanged | `term_walk::collect_top_binary_conjuncts` 61.8% |
| `array_sel` | QF_ALIA | x1.9/level from d20 | unchanged | `abv::RowCtx::abstract_with_array_eq` 7.2% + 46% allocator |
| 17 other families | — | flat | flat | — |

### The three that remain, and why two of them are not memo bugs

- **`term_walk::collect_top_binary_conjuncts`** and
  **`abv::RowCtx::abstract_with_array_eq`** produce output that is itself
  exponential in the sharing. The conjunct collector's contract says it
  *"deliberately preserves duplicates"*, so `(and v v)` over a depth-29 shared
  DAG genuinely has `2^30` leaves. **No memo can fix this** — it needs a size cap
  or a dedup contract, which is a decision about the contract and about the
  eleven call sites with "extra leaf semantics", not a cache. Left for an owner.
- **`qinst_egraph::{collect_vars, collect_app_candidates}`** (14.5% + 5.0% of
  `quant_lia` after this lane's fixes) is an ordinary memo bug and is the next
  one to take.

### Census

Token-based, approximate in both directions, reported as a lead generator.

| | branching `TermId` walkers | no memo token | with a depth cap |
|---|---:|---:|---:|
| base `a25e98639` | 216 | **164** | 5 |
| after this lane | 207 | **152** | 2 |

The 164 is not 164 bugs and was never quoted as one. Eleven left the list; of
the remaining 152, five are named above with per-file evidence and the rest are
unclassified leads.

## Real-corpus reachability: narrow, and the fix is priced accordingly

Deep `let` nesting is common; this blowup needs each level referenced at least
**twice** along one spine. Measured by computing the exact quantity that governs
the walk — `paths(n) = Σ paths(arg)` over the spine operators, `let`-bound names
resolving to the bound term's value.

| population | files scanned | `let` depth ≥ 25 | `+ - *` paths ≥ 2^20 | max `+ - *` paths |
|---|---:|---:|---:|---:|
| QF_LIA, whole division | 12,422 of 13,306 | 3,448 | **0** | 39,800 |
| QF_LIA board slice | 200 | 55 | **0** | 128 |
| QF_UFLRA board slice | 197 | 112 | **0** | 36 |
| QF_NRA board slice | 200 | 46 | **0** | 158,100 |
| QF_NIA / QF_SLIA / QF_UF / QF_UFLIA / QF_IDL slices | 997 | 56 | **0** | ≤ 374 |

Over `and`/`or` spines (the unfixed `collect_top_binary_conjuncts` instance) the
picture is the same except for one family: **QF_IDL's `Averest` sorting
benchmarks**, where `BubbleSort_safe_blmc016.smt2` has **8,394,292** and/or paths
in 1.4 MB of source — genuine sharing amplification, not size. Both arms decide
it `unsat` in 3.6 s, so even there it is not a cliff today.

Caveat on the metric: `max_paths` equals the leaf count for an UNSHARED spine,
so a large value alone is not blowup — blowup is paths ≫ nodes. The QF_NRA
158,100 and QF_LIA 39,800 rows are wide flat sums, not sharing.

So: **this is robustness, not board points.** It removes a cliff a competition
generator or an adversarial input reaches trivially and that today's public
corpora do not.

## Verification

- **Interleaved per-file A/B**, both arms back to back on one pinned core per
  worker, arm order alternating, 24 s budget, shipped `main` vs this lane.
  - **QF_LIA (200 files): 0 gains, 0 losses, 0 flips**, wall +1.2%. The raw run
    showed 2 losses; both re-checked at 4 interleaved repetitions on a quiet
    core decide `sat` in **both** arms at 15.6–18.4 s against a 24 s budget, and
    the fixed arm was faster in 6 of those 8 pairings. They are the near-budget
    class, not a regression. Raw and re-checked both reported.
  - QF_UFLRA / QF_LRA / QF_UF (control): see the lane report.
- **The five z3 differential fuzzes**, `--features z3`, nonzero counts confirmed
  for each: `qf_lra` 5, `simplex_lra_fallback` 1, `qf_uflra` 1,
  `difference_logic` 4, `qf_lia` 4 — **15 tests, 0 failures**.
- **Solver lib sweep** `--features full -- --test-threads=4`: **1722 passed,
  0 failed** (run after each of the two code commits).
- Clippy `-p axeyum-solver --all-targets --features full -- -D warnings`: clean.
  `cargo fmt --all --check`: clean.

## Guards added

- `lin_form_expands_a_shared_dag_once_per_node` — asserts the memo's EXPANSION
  COUNT (`<= 64` for a 33-node DAG with `2^31` paths), not a wall time. Delete
  the memo lookup and this is the test that dies, immediately rather than after
  an hour.
- `shared_let_chain_of_depth_40_is_decided` — the front door, asserting `sat`.
  `2^41` paths; it does not return on the unmemoised tree.

Both live in `auto.rs`'s inline test module, so they run under the existing
`-p axeyum-solver --lib --features full` pre-push gate and add no new suite for
`scripts/check-suite-gating.py` to require.

<!-- /plan-section -->
