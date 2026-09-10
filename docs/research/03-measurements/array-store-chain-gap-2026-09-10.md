# Store-chain depth costs us nothing on our own corpus, and a lot on one public family

**Date:** 2026-09-10 · **Lane:** M3-8 · **Host:** s4 (16 threads, 123 GB) ·
**Base:** `origin/main` @ `474423c8d`

Roadmap item 3.8
([`docs/solver-comparison-2026-09/11-roadmap-and-plan.md:94`](../../solver-comparison-2026-09/11-roadmap-and-plan.md))
gates on "count store-chain depth on `QF_ABV` public corpora." Item 4.2 (adopt
STP's cost-based staged eager/lazy rule) is gated on this measurement.

## 1. The question, as a number

How deep do `store(store(store(...)))` chains get in the `QF_ABV`/`QF_AUFBV`
benchmarks we are asked to solve, does depth correlate with a verdict we fail
to reach, and what does eager elimination (ADR-0010) actually cost on the
deepest ones?

**Answer, in one line per corpus:**

- **Committed/curated corpus (272 files, what CI gates on today): max depth
  79, zero depth-correlated failures, eager-elimination cost for the deepest
  chain is 81 µs.**
- **The wider public `smtlib-2024` `QF_ABV` set (15,148 files, sampled):
  depth reaches 1200, and a deliberately-constructed 104-file family
  (`brummayerbiere/wchains*`) drives eager elimination into multi-million-node
  formulas that our default solve path fails to decide (`unknown`) starting
  around depth 240–320, using up to 23 GB RSS at depth 800.**

Depth alone does not predict this: a real-world 595-file family at the same
depth (KLEE symbolic-execution traces, depth 256) solves in seconds. The cost
driver is **reads × chain length** — exactly what STP's own comment (quoted in
`docs/solver-comparison-2026-09/04-bitwuzla-boolector-stp.md:690-696`)
describes, and exactly what the `wchains` family is built to maximize.

## 2. Method

Two throwaway tools (not committed — see §7):

- `crates/axeyum-bench/examples/store_chain_depth_probe.rs`: parses a file
  with `axeyum_smtlib::parse_script`, walks the term arena for the longest
  chain of `Op::Store` nodes along the array-argument edge (memoized over the
  shared DAG, so a `let`-shared chain is O(n) not exponential), and optionally
  runs `axeyum_rewrite::eliminate_arrays` (ADR-0010's eager pass) to report
  DAG size before/after and wall time. `--skip-elim` skips the elimination
  step for a depth-only sweep. `--list <file>` reads newline-separated paths.
- The existing `crates/axeyum-bench/examples/explain_corpus.rs` is **not**
  used for verdicts — it disagrees with the shipped front door on 134/397
  benchmarks (documented in its own header and in
  `docs/contributor-guide/measurement-hazards.md`). Verdicts below all come
  from `crates/axeyum-bench/examples/smtcomp_cli.rs`, which wraps
  `axeyum_solver::solve_smtlib` — the actual SMT-COMP-interface front door.

Both examples were built via `scripts/cargo-serialized.sh` (debug for the
corpus sweep, release for the cost-curve scan below — see §5's note on why
both are reported).

## 3. Committed corpus: no problem here

```sh
grep -rl "set-logic QF_A(UF)?BV" corpus/ | wc -l   # 272 (270 real .smt2; 2 hits are READMEs)
```

270 real `.smt2` files across `corpus/regression/{cvc5/qf_abv,qf_abv}`,
`corpus/public-curated/non-incremental/{QF_ABV,QF_AUFBV}/{bitwuzla,cvc5}-regress-clean`.
`corpus/qfbv-curated` is pure `QF_BV` (43/43 files, no arrays) — excluded.

```sh
./target/debug/examples/store_chain_depth_probe --list <(the 270 files)
```

267/270 parsed (3 are parser-level `unsupported`, unrelated to arrays: a
nested-array-element sort, an unbound identifier, and `eqrange` over a
non-`Int` index — all three also come back `unknown` from `smtcomp_cli` in
~100 ms, i.e. rejected before array reasoning ever runs).

Depth distribution (267 files):

| depth | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 9 | 12 | 14 | 79 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 122 | 79 | 40 | 11 | 3 | 1 | 1 | 2 | 2 | 2 | 3 | 1 |

mean 1.48, p50 1, p90 2, p99 14, max 79.

**Cost on the deepest committed chains** (eager `eliminate_arrays`, debug
build — release is faster, see §5):

| file | depth | dag_in | dag_out | elim time |
|---|---|---|---|---|
| `solver__array__lazywritememleak1.btor.smt2` | 79 | 153 | 337 | 838 µs |
| `solver__array__fifo32{in,ia,bc}04k05.smt2` | 14 | 933–1187 | 6,902–8,056 | 13.5–16.1 ms |

**Verdicts** (`smtcomp_cli`, 10 s internal soft timeout, 15 s hard `timeout`):
134 sat, 129 unsat, 7 unknown, over 270 files, all in ≤303 ms wall time. The 7
`unknown`s are exactly the 3 parser-rejections above plus 4 more tiny files
(dag_in 9–30, depth 0–1) that fail for unrelated reasons (e.g. unconstrained
functions) — **zero of the 7 have any meaningful store-chain depth or
elimination cost.** No timeout was observed anywhere in this corpus.

**No correlation between depth and failure exists in the committed corpus** —
the deepest chain we ship (79) is the cheapest kind of `unsat`/`sat` we have.

### The two things to check

1. **`MAX_ARRAY_EQ_INDEX_BITS = 8` is a route selector, not a refusal**,
   confirmed independently. Calling `eliminate_arrays` directly (bypassing the
   lazy fallback) fails on 22/267 committed files; 13 of those 22 are array
   equalities over a 16- or 32-bit index that crosses the cap
   (`arrays.rs:461-466`). **All 22**, including all 13 cap-crossers, are
   decided (12 sat / 10 unsat, no timeout) by the shipped
   `check_qf_abv_lazy_row_warm` route, which consumes the `Unsupported` error
   as its lazy-CEGAR trigger (`abv.rs:739-744`) — exactly ADR-1814's finding.
2. **`certify_array_elim_unsat` has zero callers in `evidence.rs`**, confirmed:
   `grep -c certify_array_elim_unsat crates/axeyum-solver/src/evidence.rs` →
   `0`. Its only non-test callers are
   `crates/axeyum-machine-evidence/src/symbolic_memory.rs:344,409` — a
   different consumer, not the default solve path. So even on files this
   measurement's eager path decides cheaply (the 79-deep chain above), the
   shipped `unsat` (when applicable) carries no array-specific certificate
   today; the checkable claim eager elimination could buy is not being
   collected. This does not change §6's recommendation (below) but it does
   mean "eager buys a certificate" cannot be cited as a reason to keep the
   *uncapped* eager path once a cost predicate exists — the certificate isn't
   shipping either way, per ADR-1814.

## 4. Public corpus at scale: `smtlib-2024` `QF_ABV`/`QF_AUFBV`

`/nas3/data/axeyum/corpus/` is mounted (`nas3:/volume1/data` NFS). The full
`smtlib-2024` non-incremental sets are extracted:

```sh
find /nas3/.../non-incremental/non-incremental/QF_ABV -name '*.smt2' | wc -l    # 15,148
find /nas3/.../non-incremental/non-incremental/QF_AUFBV -name '*.smt2' | wc -l  # 75
```

42 of the 15,148 `QF_ABV` files exceed 5 MB (up to **1.17 GB** — a
`ridecore-qf_abv-bug.smt2` symbolic-execution trace that stalled a single-file
parse past a 180 s budget on the first attempt); excluded from this sweep and
noted as unmeasured (§8). The remaining 15,106 were sampled every 20th file
(756 files, depth-only, `--skip-elim`, so the sweep is a bounded single DAG
walk with no elimination blow-up risk) — **752/756 parsed.**

Depth distribution (752 files, `--skip-elim`):

| stat | p50 | p90 | p99 | max |
|---|---|---|---|---|
| depth | 0 | 8 | 256 | **1200** |

403/752 have depth 0 (no stores, or `select`-only over declared arrays); 349
have at least one store. The tail above depth 200 is concentrated in two named
families:

- **`brummayerbiere/wchains{002..500}{se,ue}.smt2`** (104 files total,
  depths 8–1200) — Boolector's own write-chain regression corpus, a
  deliberately-scaling `store`-chain-then-multi-read torture test. This is
  the exact shape the roadmap item and the STP citation describe.
- **`klee-selected-smt2/`** (595 files) — real KLEE symbolic-execution
  queries; every sampled instance sat at depth exactly 256 (matches a 256-byte
  buffer chunking convention).

Neither family is in the 272-file committed corpus (`grep -c wchains` → 2,
both depth-8; `grep -c klee` → 0).

## 5. What eager elimination actually costs on the deep tail

`wchains{N}se.smt2` scales cleanly: max depth = 4×N. Eager-elimination-only
scan (release build — debug is ~5–10× slower on this curve but agrees on
shape):

| N | depth | dag_in | dag_out | elim time (release) |
|---|---|---|---|---|
| 2 | 8 | 46 | 299 | 81 µs |
| 20 | 80 | 352 | 25,949 | 5.2 ms |
| 60 | 240 | 1,032 | 231,429 | 100 ms |
| 100 | 400 | 1,712 | 641,709 | 281 ms |
| 150 | 600 | 2,562 | 1,442,559 | 1.01 s |
| 200 | 800 | 3,412 | 2,563,409 | 1.50 s |
| 300 (earlier debug run) | 1200 | 5,112 | 5,765,109 | 16.7 s (debug) |

DAG size and elimination time both grow **roughly quadratically in depth** —
consistent with STP's own comment: "a read over a chain of WRITEs becomes one
ITE per link, so nine reads over a deep store chain expand into tens of
thousands of nodes."

**The elimination pass itself stays affordable even at depth 800 (1.5 s,
release).** The actual failure is downstream: bit-blasting and solving the
resulting 2.5M+-node `QF_BV` formula. Full-solve boundary scan
(`smtcomp_cli --timeout-ms 60000`, 90 s hard wall, **release build**):

| file | depth | verdict | wall | peak RSS |
|---|---|---|---|---|
| `wchains040se` | 160 | sat | 12.2 s | 889 MB |
| `wchains060se` | 240 | sat | 28.6 s | 1.9 GB |
| `wchains060ue` | 240 | **unknown** | 61.3 s | 1.9 GB |
| `wchains080se` | 320 | **unknown** | 61.3 s | 3.5 GB |
| `wchains100se` | 400 | **unknown** | 61.3 s | 5.9 GB |
| `wchains200se` | 800 | **unknown** | 62.0 s | **23.4 GB** |

(Debug-build boundary, for comparison: sat through depth 160 at 44 s, unknown
from depth 240 at 61 s — same shape, cliff ~1.3–2× lower depth than release.)

The `unsat` variant is harder than `sat` at the same depth (`wchains060ue`
already times out where `wchains060se` is decided in 28.6 s) — expected, since
CDCL must fully refute rather than stop at a witness.

**Depth alone does not predict this.** `klee-selected-smt2/cu-no-caches/_factor-query-004984.smt2`
(depth 256, 1,793 assertions, dag_in 4,892) solves `sat` in 18.3 s using 68 MB
RSS — two orders of magnitude cheaper than `wchains060se` at *lower* depth
(240) and *far* cheaper than anything ≥depth 320. The difference is the
**reads-per-chain-position** ratio: `wchains` is built to read from every
position along the write chain (maximizing the Ackermann pairing +
read-over-write ITE product STP's comment describes); KLEE's organic queries
read a few specific addresses from a long-lived memory chain, so read-over-write
resolution stays local and cheap.

## 6. Recommendation: **BUILD**, scoped to a cost predicate — not depth alone

- **Not urgent for the committed/curated corpus** — nothing there is deep
  enough to cost us anything (§3), so this is not blocking today's CI-gated
  numbers.
- **Real for the public corpus this project measures Z3/Boolector parity
  against.** A 104-file family already in `smtlib-2024` `QF_ABV` — plus
  presumably more in the 42 excluded >5 MB files and in `QF_AUFBV` /
  `non-incremental` sets not yet sampled — makes our default route return
  `unknown` on instances a capability-based check alone will never catch:
  **`eliminate_arrays` never returns `Unsupported` for a deep store chain by
  itself; it succeeds, slowly, at whatever size the chain demands.** ADR-1814
  is correct that the *existing* `Unsupported`-triggered lazy fallback
  (`abv.rs:739-744`) already covers the `MAX_ARRAY_EQ_INDEX_BITS` case (§3.1)
  — but that finding does not extend to plain deep store chains, because
  those never hit the `Unsupported` arm at all. There is currently **no**
  admission test — capability or cost — that would route `wchains200se` to
  the lazy-ROW path before eager elimination is allowed to build a
  2.5-million-node formula.
- **The STP-shaped predicate (reads × depth, item 4.2) is the right fix, not
  Boolector's lambda/memset recognition.** Memset/memcpy pattern recognition
  is a bigger encoding-level change (symbolic ranges) that this measurement
  gives no reason to reach for yet — a cheap **admission test before running
  `eliminate_arrays`**, routing to the already-existing (and, since item 1.1a,
  warm) lazy-ROW CEGAR path when the estimated read×depth product is large,
  would keep today's cheap cases on the fast eager path and move exactly the
  `wchains`-shaped tail off it.
- **What would raise confidence before committing to a specific threshold:**
  run the same boundary scan through the **lazy-ROW path directly** (forcing
  it, bypassing eager admission) on `wchains060`–`wchains200` to confirm it
  actually decides them fast — this measurement did not do that (§8), and if
  the lazy path is *also* slow on this shape, a cost predicate alone doesn't
  fix the underlying problem.

## 7. Probe code

`crates/axeyum-bench/examples/store_chain_depth_probe.rs` was added for this
measurement and is **not being kept** — it will be removed before this branch
merges (per the lane brief: throwaway probes don't stay live in the tree). If
a maintainer wants the depth-walk kept, the natural home is a small
`#[ignore]`d test near `axeyum_rewrite::eliminate_arrays`, not a bench
example.

## 8. What was not measured

- The 42 `QF_ABV` files >5 MB on NAS (up to 1.17 GB) — parsing risk, excluded
  entirely from the depth sweep. Unknown whether they contain deeper chains
  than the 1200 found in the sampled set.
- `QF_AUFBV` on NAS (75 files) — not depth-swept (small enough to not need
  sampling, but time ran out; likely similar shape to the committed
  `QF_AUFBV` set, which topped out at depth 14).
- The `non-incremental` public corpus beyond `smtlib-2024`'s `QF_ABV`/`QF_AUFBV`
  — did not check `_archives`/`_archives_inc` (incremental sets) at all.
- Whether the **lazy-ROW path**, forced directly, decides the `wchains` tail
  fast — this is the single measurement that would turn §6's "BUILD" into a
  concrete threshold instead of a direction. Not run here because forcing it
  requires bypassing internal dispatch logic, which is implementation work,
  not measurement, under this lane's scope.
- Boolector/STP were not run as a cross-check (`references/` clones absent in
  this worktree per the lane brief, and STP is not in
  `scripts/fetch-references.sh`'s repo list per ADR-1814). The claim that a
  memset/memcpy-aware solver would decide `wchains200se` fast is inference
  from the pattern, not a measured comparison.
- Solver behavior on the `ue` (unsat) variants beyond N=60 — only one unsat
  point was measured; the sat/unsat asymmetry at depth 240 (§5) is a single
  data point, not a curve.
