# Intern-table hasher swap, measured (2026-09-05)

Follow-up to D5/recommendation 6 in
[2026-09-05-sat-smt-performance-and-architecture-review.md](2026-09-05-sat-smt-performance-and-architecture-review.md):
"Swap the hasher. A seeded fast hasher plus `indexmap` where iteration order
is observable; measure on the intern table first." This note is that
measurement, scoped to `crates/axeyum-ir` only.

## What changed

`axeyum-ir`'s intern table (`arena.rs:44`, `intern: HashMap<TermNode,
TermId>`) and six other lookup maps used `std::collections::HashMap` with
the default SipHash-1-3 hasher and a per-process random seed. All seven,
plus the crate's memoization maps in `eval.rs`/`fmt.rs`/`stats.rs`, now go
through `FastMap`/`FastSet` — one alias pair in
[`crates/axeyum-ir/src/fast_map.rs`](../../../crates/axeyum-ir/src/fast_map.rs)
backed by `rustc-hash`'s `FxHashMap`/`FxHashSet` (`FxBuildHasher`). The
tradeoff analysis against `ahash` and `indexmap`, and the honest accounting
of what in `TermNode`'s `Hash` derive is and isn't FxHash-safe, live in that
module's doc comment rather than being repeated here.

`eval_with_memo`'s memo parameter was genericized over its hasher
(`HashMap<TermId, Value, S>` instead of the pinned default) so that
`axeyum-solver` and `axeyum-rewrite` — both out of scope for this pass —
keep compiling against a plain `HashMap<TermId, Value>` unchanged, while
`eval()`'s own internal memo now uses `FastMap`.

Scope, as directed: `axeyum-ir` only. `axeyum-solver`'s ~470
`HashMap`/`HashSet` uses (D5's table) are untouched.

## Iteration-order audit

**Method.** Every `FastMap`/`FastSet`/`HashMap`/`HashSet` type-position
occurrence in `crates/axeyum-ir/src/` (21 occurrences, `fast_map.rs`'s own
two `pub type` definitions and its doc-comment prose excluded) was checked
for every `.iter()`, `.keys()`, `.values()`, `.into_iter()`, and `.drain()`
call reachable from it. Coverage command:

```sh
grep -rn "FastMap<\|FastSet<\|HashMap<\|HashSet<" crates/axeyum-ir/src/ \
  | grep -v "crates/axeyum-ir/src/fast_map.rs:1[34][0-9]:pub type"
# 21 occurrences: 6 in arena.rs (symbol_lookup, internal_lookup,
# function_lookup, internal_function_lookup, uninterpreted_sort_lookup,
# intern), 6 in eval.rs (bindings, functions, real_div_zero, the local memo
# in eval(), the generic memo parameter in eval_with_memo, and the test
# module's memo), 2 in fmt.rs (import + memo), 2 in stats.rs (memo,
# symbols), plus fast_map.rs's own two internal HashMap/HashSet
# instantiations (the alias definitions themselves) and prose mentions.
```

Then, per site, every method call on that field/variable:

```sh
grep -n "self\.symbol_lookup\.\|self\.internal_lookup\.\|self\.function_lookup\.\|self\.internal_function_lookup\.\|self\.uninterpreted_sort_lookup\.\|self\.intern\." crates/axeyum-ir/src/arena.rs
grep -n "self\.bindings\.\|self\.functions\.\|self\.real_div_zero\." crates/axeyum-ir/src/eval.rs
grep -n "memo\." crates/axeyum-ir/src/fmt.rs crates/axeyum-ir/src/stats.rs crates/axeyum-ir/src/eval.rs
```

**Findings.**

| Map | Methods used | Iterated? | Reaches output? |
|---|---|---|---|
| `arena.rs` `symbol_lookup`, `internal_lookup`, `function_lookup`, `internal_function_lookup`, `uninterpreted_sort_lookup` (6 fields, one is `intern`) | `.get()`, `.insert()` only | No | No — point lookups only |
| `eval.rs` `bindings` | `.get()`, `.insert()`, `.len()`, `.is_empty()` | No | No |
| `eval.rs` `functions` | `.get()`, `.insert()`, `.iter()` (inside `functions()`) | Yes | **Was: yes, unsorted.** Fixed — see below. |
| `eval.rs` `real_div_zero` | `.get()`, `.insert()` (via `get_or_insert_with`), `.iter()` (inside `real_div_zeros()`) | Yes | **Was: yes, unsorted.** Fixed — see below. |
| `eval.rs`/`fmt.rs`/`stats.rs` memo tables (4 sites) | `.contains_key()`, `.insert()`, index (`memo[k]`), `.remove()` | No | No |
| `stats.rs` `symbols` (`FastSet<u32>`) | `.insert()`, `.len()` | No | No — only the count is read |

**Two live determinism bugs found and fixed**, both in `eval.rs`:

- `Assignment::functions()` iterated `self.functions` (a `HashMap`, now
  `FastMap`) directly and returned that order to callers. Callers across
  the workspace fold this into model output —
  `crates/axeyum-py/src/solver/results.rs:309` builds a Python-visible
  model from it, and a dozen-plus sites in `axeyum-solver` iterate it in
  dispatch loops. This violates the "no hash-map iteration order in
  output" hard rule in `CLAUDE.md` today, independent of this pass's
  hasher swap — it would already reorder between two runs of the same
  binary that happened to pick different SipHash seeds and print a model,
  though in practice most single-run call sites never observe two orders
  in the same process. **Fix:** `functions()` now collects into a `Vec`,
  sorts by `FuncId`, and returns `entries.into_iter()`.
- `Assignment::real_div_zeros()` had the same shape on `self.real_div_zero`
  (a `Rational`-keyed map). **Fix:** sorted by `(numerator, quotient)`
  before returning.

Both fixes are inside `eval.rs` only, change no public type, and are
backward compatible (the return type is still `impl Iterator<Item = ...>`).
`cargo test -p axeyum-ir` and the corpus regression sweep (below) both stay
green after the change, which is expected — nothing exercises a specific
raw hash order today, this was a latent risk rather than an observed
failure.

**No other iteration-order finding.** Every other map/set site in the crate
is accessed exclusively through point operations (`get`/`insert`/
`contains_key`/`remove`/`len`); none is ever `.iter()`d, `.keys()`d,
`.values()`d, `.into_iter()`d, or `.drain()`ed. The `intern` table itself
(the one this pass targeted) is one of these: `TermId` assignment happens
at insert time by reading `nodes.len()`, not by iterating the map, so it
was never a determinism risk on this axis — only a throughput one.

## Measurement

**Corpus file.** Largest `.smt2` under
`/nas3/data/axeyum/corpus/public/non-incremental/QF_BV/20221214-p4dfa-XiaoqiChen/`:
`Composition/compose.s4._bit8_na6_nr4_paired.smt2`, 17,645,542 bytes
(~16.8 MiB), 28,339 assertions, 340,646 arena nodes after parse.

**Harness.** New example
[`crates/axeyum-bench/examples/intern_timing.rs`](../../../crates/axeyum-bench/examples/intern_timing.rs)
(neither `preprocess_timing.rs` nor `measure_corpus.rs` isolates parse+intern
as its own timed stage). It times `axeyum_smtlib::parse_script`, which
interns every term through `TermArena` as it builds each assertion, so
elapsed time here is dominated by the intern table's hash/lookup/insert
path rather than any later rewrite/solve stage. Built with
`scripts/cargo-serialized.sh build --release -p axeyum-bench --example
intern_timing`.

**A/B construction.** "Before" is a `scripts/lane-snapshot.sh aa1d8938e`
extraction (the commit immediately preceding the hasher-swap commit,
`bcd986ebf`) with `intern_timing.rs` copied in unmodified (the example
itself does not touch the hasher, so it is valid to reuse verbatim against
either `axeyum-ir` build). "After" is this worktree's own release build at
`bcd986ebf`. Both built with the same `cargo build --release` flags, same
machine, same file.

**`arena_intern` criterion bench:** not present in `crates/axeyum-ir/` on
local `main` as of this measurement (`crates/axeyum-ir/benches/` does not
exist). Recommendation 3 in the review doc (micro-benchmarks for hot
paths) has not landed yet for this crate.

**Runs.** `taskset -c 0-7`, five runs each, both first as separate blocks
and then re-run as eight interleaved before/after rounds to control for
load drift (the host had a fleet load average of 25–36 on a 16-core
i5-12600K throughout this measurement — other lanes' concurrent builds —
per `uptime`; every earlier stated measurement standard here, and this
review's own §1.4, records timing numbers as advisory when that condition
holds, so this section is explicit about it rather than presenting a clean
number).

Two straight 5-run blocks (ms):

| | run 1 | run 2 | run 3 | run 4 | run 5 | min | median | max |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Before (SipHash) | 1888.865 | 1647.540 | 831.765 | 804.863 | 938.490 | 804.863 | 938.490 | 1888.865 |
| After (FxHash) | 1094.347 | 1093.546 | 1036.523 | 851.815 | 951.603 | 851.815 | 1036.523 | 1094.347 |

Read literally, the after block's min and median are both *higher* than
the before block's — the opposite of the expected direction. This is a
reference-frame artifact, not a regression: the before block happened to
land two long outliers (1888, 1647 ms, both >2x the block's own min) from a
load spike, and 5-run blocks executed minutes apart on a loaded shared host
are not a controlled comparison — exactly the "NOT COMPARABLE" condition
`docs/research/08-planning/frontier-ratchet-reference-frame.md` describes
for the solver's own frontier suite. Taking either 5-run block's own
numbers as a hasher verdict would be over-claiming.

Eight interleaved rounds (before then after, back to back, ms):

| round | before | after |
|---:|---:|---:|
| 1 | 1080.878 | 1628.579 |
| 2 | 1113.977 | 788.407 |
| 3 | 687.291 | 666.849 |
| 4 | 770.116 | 650.767 |
| 5 | 708.711 | 770.818 |
| 6 | 658.479 | 624.635 |
| 7 | 679.192 | 756.952 |
| 8 | 738.575 | 609.724 |

Pooling all 13 before-samples and all 13 after-samples (the two 5-run
blocks plus the eight interleaved rounds) for a less noise-sensitive
summary:

| | n | min | median | max |
|---|---:|---:|---:|---:|
| Before (SipHash) | 13 | 658.479 | 804.863 | 1888.865 |
| After (FxHash) | 13 | 609.724 | 788.407 | 1628.579 |

By pooled min, after is ~7.4% faster; by pooled median, ~2.0% faster. Both
directions are correct (FxHash faster) but small relative to the run-to-run
spread from fleet contention (each side's own max is 2–2.5x its own min).
**Read this as a weak, directionally-consistent signal, not a validated
speedup number** — the honest conclusion of this measurement is that the
hasher's contribution to this file's total parse+intern wall time is
modest, plausibly because parsing/tokenization and per-term `Vec`/`Box`
allocation dominate over hash computation for a corpus file whose intern
table sees mostly unique, already-distinguished term shapes rather than
heavy collision pressure. A clean number would need either a quiet host or
a proper statistical microbenchmark (recommendation 3's `criterion`-based
hot-path suite, isolating hashing/insertion from parsing) — this pass used
neither, by construction (it targeted the crate boundary, not a bench
harness, and the fleet was not idle at measurement time).

Both binaries report identical `arena_nodes=340646` and
`assertions=28339` on every run — confirms the hasher swap changed no
observable term-identity or count, as required (hash-consing correctness
does not depend on which hash function distinguishes buckets, only on
`PartialEq`/`Hash` agreement, which is unchanged).

## Correctness gates

- `scripts/cargo-serialized.sh test -p axeyum-ir`: 76 lib tests + 13 + 7 +
  2 + 2 integration tests + 2 doctests, all passing (nonzero, confirmed by
  reading the printed counts, not just exit status).
- `scripts/cargo-serialized.sh test -p axeyum-solver --features full --test
  corpus_regression`: 1 test, `corpus_regression_is_sound ... ok` (29.38s).
  This is the pre-merge gate for anything touching term identity; it is
  oracle-free but exercises real corpus files through the full pipeline,
  which is what a hash-consing change most needs to not silently corrupt.
- `scripts/cargo-serialized.sh clippy -p axeyum-ir --all-targets
  --all-features -- -D warnings`: clean.
- `cargo deny check`: `advisories ok, bans ok, licenses ok, sources ok`
  (`cargo-deny` is installed on this host).
- `scripts/cargo-serialized.sh build --target wasm32-unknown-unknown -p
  axeyum-solver`: builds clean (one pre-existing, unrelated `dead_code`
  warning in `memory_budget.rs`, not touched by this pass). `rustc-hash`
  needs no wasm-specific feature work, confirming the doc comment's claim.

## Recommendation

**Do not prioritize the `axeyum-solver` ~470-map sweep on this
measurement alone.** The evidence for the hasher swap's value here is (a)
removing a real, if narrow, iteration-order determinism bug class (the two
`eval.rs` fixes — these are unambiguous wins independent of speed), and
(b) a directionally-correct but small (2–7%, noisy) throughput edge on one
large real corpus file whose workload is parse-and-allocate dominated, not
hash-dominated. A crate with 550 `BTreeMap` + 311 `HashMap` uses in genuine
CDCL(T)/simplex/e-graph hot loops (D5's numbers) is a different workload
shape — tight lookup loops over small keys in the solver's search core are
exactly where SipHash's per-call constant overhead is proportionally
larger and FxHash's advantage should show more clearly — but that is a
hypothesis this measurement does not test, and D5's own recommendation
("measure on the intern table first") has now been done honestly rather
than assumed. Before dispatching that lane: (1) get a real number from
recommendation 3's hot-path micro-benchmarks (`CdclT::propagate`, simplex
pivot, e-graph merge — none of which this measurement touched) on a quiet
host or via `criterion`, since CLI wall-clock timing on a loaded fleet
host cannot distinguish a 5–15% win from noise as this note's own numbers
show; and (2) budget for `axeyum-solver`'s BTreeMap-heavy hot paths
separately from its HashMap-heavy ones, since D5 groups both under "the
hasher" but only the latter is this lane's finding.
