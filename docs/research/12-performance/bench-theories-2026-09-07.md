# bench-theories diary — 2026-09-07

Lane `bench-theories`. Scope: simplex, congruence closure (`axeyum-egraph`),
difference logic (`dl_online.rs`), the int-blast width ladder
(`axeyum-rewrite::int_blast` + `auto.rs`), `eliminate_arrays`,
`eliminate_int_divmod`. Brief: add criterion benches for the uncovered paths,
find where the time actually goes in two or three hot theory paths at the
level of a named function and data structure, keep a diary including where I
was wrong.

Machine: local dev box (s4) for orchestration and the one-off z3 differential
fuzzes (z3 is not installed on s6 — no `pkg-config`, no `libz3*` under
`/usr/lib/x86_64-linux-gnu`); all cargo builds/benches/timing runs on **s6**
(16 cores, ~26 GiB), reached via `ssh s6` since `scripts/lane-snapshot.sh`'s
default scratch root (`/data0/axeyum`) does not exist there — s6 has no
`/data0` at all, only the 89 GiB-free root disk. Used a plain `rsync
--exclude=target --exclude=.git` into `~/bench-theories-src` on s6 instead,
with `CARGO_TARGET_DIR=~/bench-theories-target`, and committed only from this
worktree on s4. `/proc/loadavg` on s6 before any run: `1.13 1.03 1.01`
(idle). It climbed to `6.25` after a `--features full` compile (my own
`cargo` parallelism, `nproc`=16) and settled back down; every *timed* number
below was taken with s6 otherwise idle (no other lane observed on it).

## What shipped

Four criterion benches for the four routes named in the brief as uncovered,
all `harness = false`, all building and running clean:

- `crates/axeyum-rewrite/benches/eliminate_arrays.rs` — two fixtures:
  `eliminate_arrays_many_reads_quadratic` (N reads of one array under N
  distinct indices) and `eliminate_arrays_read_over_write_chain` (a chain of
  stores under one final select).
- `crates/axeyum-rewrite/benches/eliminate_int_divmod.rs` — two fixtures:
  `eliminate_int_divmod_many_constant_groups` (N independent
  `div`/`mod`-by-constant groups) and
  `eliminate_int_divmod_zero_divisor_congruence` (`MAX_CONGRUENCE_GROUPS` = 48
  `div`-by-**literal-zero** groups — the underspecified-divisor corner this
  repo's Hard Rules name explicitly).
- `crates/axeyum-rewrite/benches/int_blast_ladder.rs` — `blast_integers` at
  widths 8/16/32/64 on a mixed linear+nonlinear (`int_mul`) `QF_NIA`-shaped
  fixture, proxying the per-rung cost of `auto.rs`'s
  `dispatch_int_blast_width_ladder`.
- `crates/axeyum-solver/benches/dl_negative_cycle.rs` (`required-features =
  ["full"]`) — a 400-edge `QF_IDL` precedence chain, satisfiable
  (`dl_online_chain_sat`) and with one closing edge forcing a whole-chain
  negative cycle (`dl_online_chain_cycle_unsat`), driven through the real
  `check_auto` dispatch (not a private struct — `dl_online`'s internals are
  all crate-private, unlike `simplex::Incremental`, so this goes through the
  public front door end to end rather than isolating just the graph engine).

Registered in each crate's `Cargo.toml` (`axeyum-rewrite` had no
`[dev-dependencies]`/`[[bench]]` section at all before this; added
`criterion.workspace = true` and three `[[bench]]` entries).

One diagnostic-only addition to `axeyum-egraph` (not a bench): a
`proof_reroot_steps` counter on `EGraph`, incremented in `add_proof_edge`'s
save-walk, with a `pub fn proof_reroot_steps(&self) -> u64` accessor. Used
below to test — and reject — my first hypothesis for the congruence-closure
hot path. All 35 existing `axeyum-egraph` unit tests still pass unchanged.

## Numbers (first pass, `--quick` criterion, s6, idle)

```
eliminate_arrays_many_reads_quadratic       ~968 µs   (N=60 reads: 60 + 60*59/2 = 1830 assertions)
eliminate_arrays_read_over_write_chain      ~126 µs   (200-store chain)
eliminate_int_divmod_many_constant_groups   ~796 µs   (200 groups, 400 assertions)
eliminate_int_divmod_zero_divisor_congruence ~719 µs  (48 groups, 1128 pairwise congruence lemmas)
int_blast_ladder_rung_width_{8,16,32,64}    ~41-42 µs each, flat across width
dl_online_chain_sat                         ~3.62 ms  (400-edge chain, check_auto end to end)
dl_online_chain_cycle_unsat                 ~3.45 ms  (same + 1 closing edge, forces a whole-chain cycle)
```

These are first-pass `--quick` numbers (fewer criterion samples than a full
run), good enough to sanity-check the fixtures and see gross shape, not yet a
tuned statistical baseline for a ratchet.

### Finding 1 — the int-blast ladder's per-rung cost is width-invariant

`blast_integers` costs the same (~41-42 µs) at width 8 as at width 64 on the
same fixture. Reading `int_blast.rs` explains why: the rewrite is a single
memoized pass over the term DAG (`Blaster::rewrite`, `term_memo`), and a
constant's *encoding* at a wider width is still O(1) work per term — nothing
in the pass scales with the bit-width itself, only with assertion/term count.
**Consequence for the ladder in `auto.rs`:** `dispatch_int_blast_width_ladder`
tries a *dense range* of widths in sequence
(`INT_BLAST_MIN_WIDTH..=INT_BLAST_DENSE_MAX_WIDTH`) until one replay-checks —
since `blast_integers` itself is flat in width, the ladder's *rewrite* cost is
linear in **the number of rungs tried**, not compounding with how wide those
rungs are. The dominant cost of a ladder run is therefore however many widths
get tried before one sticks (or the ladder exhausts), each paying the SAT
solve at that width, not the blast. This says the highest-leverage
optimization for the ladder is fewer rungs (a better first-width heuristic or
early-exit signal), not a faster blast — the blast is already cheap and flat.
I did not instrument the actual dense-range rung count on a real corpus file
to confirm how many rungs a typical `QF_NIA` query burns before deciding;
that is the natural next measurement and I did not get to it (the `auto`
dispatch internals needed to count rungs live behind `feature = "full"` in a
different crate and I ran out of budget — recorded as **did not run**).

### Finding 2 — `eliminate_arrays`/`eliminate_int_divmod`'s pairwise passes are quadratic, and this repo's own regression corpus does not exercise them at scale

Both preprocessing routes have a documented pairwise cost (`eliminate_arrays`
via the Ackermann disequation between every pair of reads into one array,
already pinned by the existing test
`abstraction_does_not_materialize_quadratic_select_pairs`;
`eliminate_int_divmod` via `emit_zero_divisor_congruence`'s pairwise
congruence lemmas over `div`/`mod`-by-**literal**-zero groups, capped at
`MAX_CONGRUENCE_GROUPS` = 48). The new benches make both visible directly
rather than only through an assertion-count check.

**Where this proxy fails to predict, honestly reported per the brief's
warning:** I went looking for a real corpus file to validate the "many reads
into one array" and "many zero-divisor groups" shapes against, and this
repo's committed corpus does not have one. Every `QF_ABV` file under
`corpus/regression/` (the hand-written ones and the imported `cvc5` regression
slice) has at most 9 `select`/`store` occurrences total — nowhere near the
N=60 (1,830-assertion) shape the bench uses, which itself was chosen to be
comfortably inside a sub-5-minute bench, not because it matches an observed
corpus file. I did not find *any* `QF_IDL`/`QF_RDL` file in the corpus either
(`grep -l "QF_IDL\|QF_RDL"` over every `.smt2` in `corpus/` returned nothing),
so the `dl_negative_cycle` bench has no real-file counterpart to validate
against in this repository at all. **This is the finding, not a gap in the
finding:** the quadratic-pairwise routes and the difference-logic route are
exercised today only by hand-written unit/regression fixtures at trivial
scale; nothing in the committed corpus would surface either the array-read
quadratic blowup or a difference-logic query at the size this lane's chain
fixture uses. Whether that is because such queries do not occur in the public
corpora this repo draws from, or because the corpus simply has not been
populated with array/DL-heavy files yet, is not something I determined —
recorded as **did not run** (no real-corpus validation for either headline
bench).

### Finding 3 (the "where I was wrong" one) — congruence closure's superlinear cost is NOT the proof-forest re-root walk

**Starting hypothesis**, formed by reading `EGraph::merge` → `process_pending`
→ `add_proof_edge` → `reroot_proof_tree` before measuring anything: the
proof-forest re-root walk in `add_proof_edge` (which saves and reverses the
parent-pointer chain from the merged node up to its old proof-tree root) looks
like the classic union-find-without-path-compression trap — the crate's own
doc comment on `find` says path compression is *deliberately omitted* "so the
union-find is cheaply backtrackable", trading it for union-by-size instead.
My prior was that the *proof forest* (a separate structure from the
union-find, walked by `add_proof_edge` and never compressed at all) was where
that trade-off's cost actually landed, growing without bound over a long merge
chain.

**Scaling probe** (existing `congruence_chain` bench fixture,
`CHAIN_LEN` swept 200 → 12,800, i.e. 64×, s6 idle, `--quick`):

```
CHAIN_LEN    time
    200      137.5 µs
    800      595.8 µs   (4.3x time for 4x N)
  3,200      5.20 ms    (8.7x time for 4x N)
 12,800      65.2 ms    (12.6x time for 4x N)
```

Wall time grows **~64× → ~475×** — clearly superlinear, trending toward
quadratic as N grows, not the near-linear a healthy union-by-size structure
should give. Consistent with the hypothesis so far.

**Wiring the counter, then looking** (per this lane's explicit brief warning
— a ratio alone is not a diagnosis): added `EGraph::proof_reroot_steps`,
incremented once per node visited in `add_proof_edge`'s walk, and reran the
same sweep plus two larger sizes via a standalone probe (not the criterion
bench — `cargo run --release` against `axeyum-egraph` directly, printing the
counter):

```
chain_len=   200  reroot_steps=599      (≈ 3N - 1)
chain_len=   800  reroot_steps=2,399    (≈ 3N - 1)
chain_len= 3,200  reroot_steps=9,599    (≈ 3N - 1)
chain_len=12,800  reroot_steps=38,399   (≈ 3N - 1)
chain_len=25,600  reroot_steps=76,799   (≈ 3N - 1)
```

**The counter disproves the hypothesis.** Total re-root steps are *exactly*
linear (`3N - 1`) across every size tried — the re-root walk is not the
superlinear cost. For this specific chain-merge pattern, `add_proof_edge`'s
`x` argument is always a node with no proof-parent yet (the freshly-touched
side of a fresh union), so each walk is O(1) amortized; the doc comment's
claim about the union-find (`find` is O(1) here in practice, since union-by-size
always keeps the same root and every new leaf attaches to it directly, one
hop, never node-to-node) also checked out on inspection and did not need a
counter to see.

**Phase-split timing** (a second standalone probe, `Instant`-timed `add` /
`merge` / `explain` phases separately, same fixture, s6 idle):

```
chain_len   add          merge            explain
    200     106.6 µs      107.2 µs          9.1 µs
    800     271.5 µs      908.0 µs         26.7 µs
  3,200     1.11 ms       11.04 ms         98.1 µs
 12,800     6.57 ms      153.42 ms        385.0 µs
 25,600    12.28 ms      575.85 ms        799.5 µs
 51,200    18.87 ms       2.194  s       1.712 ms
```

`add` and `explain` scale close to linearly (`add`: 256× N → 178× time;
`explain`: 256× N → ~190× time). **`merge` alone is the superlinear cost**
(800 → 51,200 is 64× N → 2,416× time, exponent ≈1.87 — essentially
quadratic), and it is not the re-root walk (confirmed linear above).

**Reading `process_pending` for the real culprit**
(`crates/axeyum-egraph/src/lib.rs`, in the loop body after a union commits):

```rust
let child_declarations = self.nodes[child.index()].class_declarations.clone();
if child_declarations.iter().any(|declaration| {
    self.nodes[root.index()].class_declarations.binary_search(declaration).is_err()
}) {
    let old = self.nodes[root.index()].class_declarations.clone();
    self.nodes[root.index()].class_declarations.extend(child_declarations);
    self.nodes[root.index()].class_declarations.sort_unstable();
    self.nodes[root.index()].class_declarations.dedup();
    self.trail.push(Undo::ClassDeclarationsReplaced { node: root, old });
}
```

In the bench's fixture every leaf carries a **distinct** declaration id
(`i` in `0..=CHAIN_LEN`), so on nearly every merge the child contributes a
declaration the root's `class_declarations` doesn't have yet: `old` clones the
root's *entire accumulated list* (an O(k) clone where `k` is however many
distinct declarations have merged into the root so far), then the merged list
is **fully re-sorted and deduped** (`sort_unstable` + `dedup`, another O(k log
k)) rather than merging two already-sorted slices in O(k) or doing a sorted
insert in O(log k + k). Over a chain of N such merges, `k` grows from 1 to N,
so total cost is `Σ_{k=1}^{N} O(k log k)` — the near-quadratic shape measured.

**Targeted A/B, to close the loop rather than stop at a plausible read**: reran
the phase-split probe with a fixture where every leaf still gets its own
distinct atom (so the union-find/proof-forest work is unchanged — real merges,
not hash-consing no-ops) but is wrapped so the only declaration that ever
reaches the growing chain class is a single shared one (`class_declarations`
never grows past length 1, so the `binary_search` finds it immediately and the
clone/extend/sort/dedup block never runs):

```
                          merge time
chain_len   growing decls   flat decls (same chain length, same # of real merges)
    200        104.3 µs        44.8 µs
    800        912.2 µs       180.5 µs
  3,200       11.33  ms       630.5 µs
 12,800      154.83  ms       3.29  ms
 25,600      574.23  ms      13.43  ms
 51,200        2.187  s      30.15  ms
```

**72× faster at N=51,200 for the identical chain length and identical number
of real merges**, and the flat-declarations column is now close to linear
(64× N → ~167× time, versus 2,416× for the growing-declarations column). This
is the same shape as the simplex finding this lane's brief cites (the pivot's
"one redundant O(rows×columns) pass") — a full clone + full re-sort of a
monotonically growing per-class list, on every union, when only a
sorted-merge or single-element insert was needed.

**Where this matters in practice, and where I did not verify it**: this cost
only shows up on a merge chain whose classes accumulate many *distinct*
declarations — i.e., congruence closure over many syntactically different
ground terms getting unioned into few classes (a large `distinct`/theory-lemma
closure, or heavy `enumerate_apps`/pattern-matching workloads that see many
declaration ids merge together). A chain of merges that stays within a small
declaration alphabet (e.g. repeated uses of the same handful of function
symbols) would not trigger it. I did not check how large `class_declarations`
typically grows on a real corpus file's EUF closure — that would tell us
whether this is a real bottleneck in practice or only in adversarial/synthetic
chains; recorded as **did not run**. I also did not attempt a fix (replacing
the clone+extend+sort+dedup with a linear merge of two already-sorted slices,
or a proper sorted insert) — this is scoped as a finding for a future slice,
not a patch in this lane, per the "did not run" discipline rather than
overclaiming a fix I have not tested against the existing 35-test suite plus
the scope-depth/backtracking tests specifically (`Undo::ClassDeclarationsReplaced`
would need to keep working under `pop`).

### Finding 4 — DL sat vs. unsat cost through `check_auto` is nearly identical at this chain length

`dl_online_chain_sat` (3.62 ms) and `dl_online_chain_cycle_unsat` (3.45 ms,
the version with one closing edge that forces a negative cycle spanning the
*entire* 400-edge chain) are within ~5% of each other. That is mildly
surprising — a worst-case, whole-chain cycle detection plus a Farkas
re-verification pass "should" cost more than pure propagation with no cycle
ever closing — but I did not instrument `dl_online.rs` itself (its `DlGraph`,
`Scratch`, and the Cotton–Maler `γ`-propagation are all crate-private, not
reachable from a bench without adding `bench_internals` exposure the way
`simplex::Incremental` has). Both numbers include the same `check_auto`
front-door overhead (parsing/dispatch/CDCL(T) driver setup) which, at 400
constraints, may simply dominate whatever the graph engine itself does either
way. **I did not separate front-door overhead from DL-engine cost** — that
needs the same `bench_internals`-style exposure the simplex bench already has
for `Incremental`, and I ran out of budget to add it for `DlGraph`/`DlTheory`
in this pass. Recorded as **did not run**; the natural next step for whoever
picks this back up is exposing `DlTheory`/`DlGraph` through
`bench_internals` (mirroring `Incremental`) so the graph engine can be timed
in isolation from CDCL(T) dispatch, the way `simplex_pivot.rs` already does
for simplex.

## What I did not get to

- No real-corpus validation for any of the four new benches (Finding 2) —
  this repo's corpus does not currently contain shapes at the scale the
  benches probe.
- Did not count actual int-blast-ladder rungs tried on a real `QF_NIA` file
  (Finding 1).
- Did not expose `DlTheory`/`DlGraph` through `bench_internals` to separate
  DL-engine cost from `check_auto` front-door overhead (Finding 4).
- Did not attempt a fix for the `class_declarations` clone+resort defect
  (Finding 3) — flagged for a future slice.
- Simplex already has a bench and was already profiled by a prior slice per
  this lane's brief; I did not re-derive that finding, only left the existing
  bench as-is (did not extend it further given the other three routes had
  none at all).
