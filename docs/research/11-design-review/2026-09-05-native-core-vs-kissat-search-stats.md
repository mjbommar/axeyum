# Native core vs Kissat/CaDiCaL: search statistics, not just decided-count

Lane `sat-stats-vs-kissat`. Gate (b)
([`2026-09-05-gate-b-sat-core-measured.md`](2026-09-05-gate-b-sat-core-measured.md),
artifact under `bench-results/sat-core-gate-b-20260905/`) measured that our
native CDCL core decides 6 of 113 p4dfa CNFs in 20 s against Kissat's 11 and
CaDiCaL's 10, and named exactly what it did not establish: *"no profiling was
done to explain why CaDiCaL/Kissat decide the extra p4dfa files."* The parent
[performance and architecture
review](2026-09-05-sat-smt-performance-and-architecture-review.md)'s
recommendation 4 (§4) points at the `CdclT` engine's architecture — no clause
arena, no blocking literals, no interleaved inprocessing (D6) — as the likely
next lever. That diagnosis is about `CdclT`, the CDCL(T) driver every
non-QF_BV division runs on; it says nothing yet about whether the SAME
explanation (inprocessing, or more generally simplification/heuristics) also
accounts for the gap on the **native proof-producing core** measured in gate
(b), which is a different, pure-CNF engine. This note is the cheap way to
replace that open guess with a measurement: compare the two solvers' own
internal search statistics (conflicts, propagation rate, and — critically —
the fraction of wall time each solver's own profiler attributes to
inprocessing vs. core search) on identical CNF, rather than only comparing
decided/not-decided counts.

## Method

**Population.** 20 of the 113 p4dfa files from gate (b)'s
`per-file-p4dfa.tsv`: the 11 files Kissat decided within its 20 s budget
(Group A, the *entire* such population, not a sample) plus 9 more it did not,
chosen to span the size range 40K-3.1M CNF variables and to include
`compose.p3.*` (Group B), where the native core and CaDiCaL both decide but
Kissat did not at 20 s. Full list, with the reasoning, in
[`bench-results/sat-stats-vs-kissat-20260905/file-list.txt`](../../../bench-results/sat-stats-vs-kissat-20260905/file-list.txt).

**Build.** CaDiCaL 3.0.1 (commit `c60730422e758ef1cebe7aeddf2dda31c996bf04`)
and Kissat 4.0.4 (commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`) — the
exact commits gate (b) used — rebuilt on the measurement host (s7) from
GitHub tarballs at those pinned SHAs (the shared checkout's
`references/{cadical,kissat}` clones from the gate (b) lane were not present
in this worktree's gitignored `references/`, so a `git clone` there would
have fetched an unpinned HEAD; a tarball at the exact SHA reproduces the
same build without that risk). Both configured/built with their own
`./configure && make`; versions confirmed via `VERSION` files and `--version`
after build.

**DIMACS.** `crates/axeyum-bench/examples/dump_dimacs.rs` (pre-existing,
unmodified) re-dumped the 20 files on s7; variable/clause counts matched gate
(b)'s recorded values exactly (cross-check, not re-derivation).

**Native core instrumentation.** `axeyum_cnf::ProofSearchProgress`
(`crates/axeyum-cnf/src/proof_sat.rs`) was read before writing any code: it
carries `conflicts`, `learned_clauses`, `proof_steps`, `proof_bytes`, and
`elapsed` — a cumulative snapshot, polled via
`solve_with_drat_proof_with_limits_and_progress`. **It does not carry a
decision counter or a propagation counter, and never exposes the `Cdcl`
struct's private `restart_count`.** This is a measured absence, not a gap in
this note's tooling: adding those counters would be a production change to
`axeyum-cnf`, out of scope for a measurement lane. A new example,
`crates/axeyum-bench/examples/native_core_stats.rs` (no `required-features`
gate — it uses only the default public API), solves one DIMACS file under a
wall-clock budget and prints verdict/wall time/conflicts/learned/proof
size as one JSON line, `null` for the three unavailable fields rather than a
fabricated number. Clippy-clean, rustfmt'd, committed.

**Kissat/CaDiCaL statistics.** `kissat -s --time=<N>` (`-s` /
`--statistics=true` — verified byte-for-byte equivalent statistics and
profiling sections to `-v`, ~2.4x fewer lines, since `-v` also logs every
internal allocator resize) and `cadical -v -t <N>`, both `taskset -c 0-7` on
the same idle 16-core host as the native core runs, 60 s per file (not gate
(b)'s 20 s — chosen so more of the population reaches a verdict for the
statistics comparison; this measurement is therefore not a re-run of gate
(b)'s decided/not-decided counts at the same budget, and two Group B files
that were "unknown" for Kissat at 20 s — `compose.p3`, `tcp_open` — decide at
60 s).

**Avoiding a double-counting trap.** Both solvers' `-v`/`-s` profiling
sections list many named "phases" (Kissat: `search`, `focused`, `stable`,
`probe`, `simplify`, `vivify`, `congruence`, `preprocess`, `substitute`,
`sweep`, `backbone`, `parse`, `transitive`, `lucky`, `reduce`, `walking`,
`extend`; CaDiCaL similarly). **A flat sum of every line was tried first,
produced impossible results (up to 129% of total wall time attributed to
"inprocessing"), and was rejected.** These profiling blocks are a call tree,
not a flat partition: Kissat's `focused` + `stable` sum to `search`
(children), and everything else (`simplify`, `vivify`, `congruence`,
`preprocess`, `substitute`, `sweep`, `backbone`, `transitive`, `reduce`,
`walking`) nests inside `probe` — confirmed arithmetically, `search + probe +
{parse, lucky, extend}` reproduces the reported total to within ~2% on every
file. CaDiCaL's `unstable` + `stable` sum to `search`, and everything else
(`elim`, `congruence`, `sweep`, `subsume`, `probe`, `vivify`, `backbone`)
nests inside `simplify` — same check, same ~2% tolerance. So `search` vs.
`probe` (Kissat) / `simplify` (CaDiCaL) is the correct, non-overlapping
top-level split, and each solver's own profiler is already computing exactly
the number this note needs (the two names differ but mean the same thing:
"time not spent in core CDCL search").

**Cross-engine soundness check.** Every `sat` verdict from `native_core_stats`
is checked against the formula with `CnfFormula::evaluate` before being
printed (`model_checked` field). Across all 20 files x up to 3 engines, **0
verdict disagreements** where at least two engines decided the same file —
no P0 finding.

Full table, raw per-file outputs (Kissat/CaDiCaL model dump `v` lines
stripped — pure noise for this question, and one file's raw text was 11 MB
of them for 16 KB of actual statistics), and the two ratio computations are
in
[`bench-results/sat-stats-vs-kissat-20260905/comparison-table.md`](../../../bench-results/sat-stats-vs-kissat-20260905/comparison-table.md)
and
[`native-table.md`](../../../bench-results/sat-stats-vs-kissat-20260905/native-table.md).

## Results

**Q1 — on the 11 files (10 non-trivial) all three engines decide**, native
core vs. Kissat:

| | conflicts (native/kissat) | conflicts/s (native/kissat) |
|---|---:|---:|
| geomean, all 10 | 0.503 | 0.612 |
| geomean, excluding 2 outliers | 1.362 | 0.775 |
| median, all 10 | 1.382 | 0.637 |

Two files (`compose.p2`, `compose.p3`) are outliers where the native core
happens to find a satisfying assignment in a handful of conflicts (40 and
128) against Kissat's thousands (8,900 and 10,709) — a lucky decision
trajectory on those two instances specifically, not a general pattern; they
pull the geomean of all 10 below 1 in a way the median (which is not swayed
by two extreme values) does not reflect. **Excluding those two, on 8 of 10
non-trivial files the native core needs more conflicts than Kissat (median
1.38x) and on every one of those 8 it processes conflicts more slowly
(median 0.637x Kissat's rate, i.e. Kissat does ~1.57x more conflicts/second)
— except two `mobiledevice` files, where the native core's raw
conflicts/second exceeds Kissat's (1.34x, 1.43x) despite needing more
conflicts overall.**

**Q2 — on files the native core does not decide in 60 s but Kissat does**,
Kissat's own profiler:

| reading | n | mean search% | mean probe%(inprocessing) |
|---|---:|---:|---:|
| strict (native and CaDiCaL both fail) | 1 | 78.9 | 15.4 |
| broad (native fails, CaDiCaL may succeed) | 3 | 67.7 | 21.6 |

For comparison, across the 10 non-trivial files all three engines decide,
Kissat's mean `probe%` is 30.1 (range 20.8-40.9) — **the same order of
magnitude as on the files the native core cannot reach**, not a jump.
Kissat's `search%` never drops below 45.5 across all 20 files measured
(mean 58.7, range 45.5-100.0); `probe%` averages 25.7 across the 19 files
where any inprocessing ran at all (`simple_*` is a trivial 0-conflict
instance with no inprocessing).

## Verdict on the inprocessing guess: mixed, leaning refuted for the strong
form, plausible as a partial contributor

**Refuted, strong form** ("the gap to Kissat is because Kissat spends its
extra time/budget doing inprocessing that our native core skips"): Kissat's
own profiler attributes the **majority of its wall time to core CDCL
search on every file measured, including the files it alone decides**
(51-100% search, mean 58.7%). Inprocessing (`probe`) is a real but minority
cost (13.8-40.9%, mean 25.7%), and it is not larger on the files that
separate Kissat from the native core (21.6-31.2% there) than on the files
all three engines decide (30.1%). If inprocessing were the dominant lever,
Kissat's own accounting would show it spending most of its *extra* time
there specifically on the hard files; it does not.

**Partially supported, weaker form** ("the gap has more than one cause, and
raw search throughput is at least as large a factor as inprocessing"): on
the 8 non-outlier files all three engines decide, Kissat processes conflicts
15-136% faster than the native core (conflicts/s ratio 0.463-1.433, median
0.637 i.e. ~1.57x), and on most (6 of 8) of those files also needs somewhat
fewer conflicts (median 1.38x more for native) — both a raw propagation/data-
structure throughput gap (two-watched-literal implementation details,
blocking literals, arena layout) and a moderate heuristic/conflict-count gap
are visible in the same data, and this note's data does not decompose how
much of the conflict-count difference (as opposed to the per-conflict rate)
is itself downstream of Kissat's inprocessing reducing problem size before
search starts. So: the pure "it's inprocessing" guess is not what the data
shows, but inprocessing is not ruled out as *one* contributor to the smaller
(median 1.38x) conflict-count gap — it is ruled out as the *dominant*
explanation, since search time dominates Kissat's own budget throughout.

## What this does not establish

- **The native core's own time breakdown is not measured at all** — no
  decision counter, no propagation counter, no restart counter exists in
  `ProofSearchProgress` to compare against Kissat's `search%`/`probe%` split
  on the native side. This note only shows Kissat's own time is
  search-dominated; it cannot show whether the native core's per-conflict
  cost is dominated by propagation, clause management, or something else.
  Adding that instrumentation is a production change to `axeyum-cnf`
  (`ProofSearchProgress`), explicitly out of scope for this measurement
  lane — a natural next step for a lane that owns that crate.
- **20 files, one host, one run each** — no repeated trials, no variance
  bars. The two `compose.*` outliers show single-run search trajectories can
  be highly sensitive to tie-breaking; a different VSIDS seed on the native
  core could move any individual file's ratio substantially even if the
  aggregate picture holds.
- **60 s budget, not gate (b)'s 20 s** — chosen to get more files to a
  verdict for the statistics comparison; this is a different, not-directly-
  comparable measurement from gate (b)'s decided-count table (two Group B
  files flip from "unknown" to "decided" for Kissat between 20 s and 60 s).
- **This says nothing about `CdclT`**, the CDCL(T) engine every non-QF_BV
  division actually runs on (D1/D2 of the parent review) — this whole
  experiment is the native proof-producing core on pure Boolean CNF, exactly
  as gate (b) was.

## Files

- [`bench-results/sat-stats-vs-kissat-20260905/`](../../../bench-results/sat-stats-vs-kissat-20260905/) —
  `file-list.txt`, `dump-stats.tsv`, `native-table.md`, `comparison-table.md`,
  `raw/{native,kissat,cadical}/*` (raw solver output, `v` lines stripped for
  kissat/cadical).
- `crates/axeyum-bench/examples/native_core_stats.rs` — new, committed.
