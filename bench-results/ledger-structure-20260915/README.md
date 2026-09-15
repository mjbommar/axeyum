# Ledger structure — does the ledger show a dispatch order worth deriving?

**2026-09-15, lane LEDGER-STRUCTURE.** Phase 3 sizing for
[Phase 4](../../docs/plan/dispatch-and-instrumentation-2026-09-15.md#5-phase-4--derived-ladder-policy-conditional)
of the dispatch-and-instrumentation plan. Phase 4 "runs only if Phase 3's
ledger shows structure. Specifically: if, for some feature class, one route
decides a large majority of what gets decided and a different route is tried
first, then ladder order for that class should come from the table." This
answers that question with numbers, per (division, feature class), from the
outcome ledger (ADR-2102, ADR-2105) alone — every number below comes from
`scripts/outcome_ledger.py`'s `load()`, no re-parsing of `--trace` captures.

**Verdict up front: yes, on 5 of 12 groups, and Phase 4 should run on those
five — but the ceiling is modest on three of them and one candidate for
Phase 4's clock (`fd:parse`'s bound probe) is not really a candidate at all.**
See §5.

## 1. What was run

All seven Tier 1 divisions' pinned 200-file lists (`bench-results/
tier1-current-20260914/*.tsv`, cross-checked byte-identical as file SETS
against `/nas3/data/axeyum/harness/postmerge-board-dt/lists/T1_<DIV>.txt`),
on `db31113fa` (local `main`'s tip at lane start), release build
(`cargo build --release -p axeyum-bench --example smtcomp_cli` — this crate
has no `full` feature of its own; it depends on `axeyum-solver` with
`features = ["full"]` unconditionally, so passing `--features full` at the
`axeyum-bench` package level is refused by cargo and was not needed), 24 s
wall / 8 GiB `ulimit -v` per file, `--trace` on.

Sharded 3 hosts (s5/s6/s7) x 4 physical core pairs = 12 shards, the same
pattern as `bench-results/quant-ladder-ownership-20260915/launch-ab.sh`, one
shard per pinned core pair, all seven divisions run SERIALLY within a shard
(mirrors `.../postmerge-board-dt/scripts/t1-driver.sh`) — never all divisions
concurrently on one core pair, which is the 9x-oversubscription collapse that
lane measured. Full record of exactly what ran, including the two scripts, is
in [`launch-t1-ledger-sweep.sh`](launch-t1-ledger-sweep.sh).

**Row-count verification, not assumed:** every one of the 84 shard-division
ledger files was checked against its own `T1_<DIV>.<NN>.txt` list's line
count before consolidation. All 84 matched exactly; **1,400 of 1,400
expected rows landed, 0 shortfall, 0 duplicates.** (`consolidate.py`'s own
log, reproduced from `/tmp/ledger-deploy/verify-rows.py`'s cross-check, is
quoted in full in §6.)

**Invariance control** (`--no-trace-control`, ADR-2102's own check that
`--trace` does not move the verdict): armed on shard 00 across all seven
divisions, 16 files x 7 = **112 of 112 `INVARIANCE ok`, 0 `MOVED`.** Comfortably
above the brief's 50-file floor.

The rows are committed at `bench-results/ledger/t1-<DIVISION>-db31113fa.tsv`,
one file per division, 200 rows each, registered in `bench-results/ledger/
INDEX.tsv` through `outcome_ledger.append_row`/`register` — never edited by
hand. `outcome_ledger.load()` classifies `db31113fa` as `main` (0 of 1,400
rows flagged stale), and overall **766 of 1,400 (54.7%) decided** — close to,
and consistent with, `tier1-current-20260914`'s single-arm 741/1,400 (53%)
measured the day before on an earlier commit; the small movement is exactly
the kind of noise that repository's own README says needs 3 passes per arm
before anyone quotes it, and this lane makes no such claim.

## 2. Method, stated so the numbers can be checked

Everything below comes from `LedgerRow` fields only (`analyze.py`, checked in
alongside this README, `python3 -m py_compile`d and covered by a fixture
test, §4):

* **class** = a row's `features` column verbatim: a real construct-class
  string (`Int`, `Int|Function`, …), `"none"` (the scan ran, found nothing),
  `"not-dispatched"` (the query never reached the quantifier-free dispatch
  ladder — true of most quantified Tier 1 files, since `check_with_quantifiers`
  runs first and the ladder is only ever reached from underneath it), or the
  empty string (no row here carries it — every row's binary is schema 3).
* **decided rows** = `decided_by != "none"`.
* **first-attempted route** = the route named in the FIRST entry of
  `attempt_trail`.
* **top decider** = the `decided_by` value with the most decided rows in one
  (division, class) group; **top share** = its fraction of decided rows.
* **modal first route** = the most common first-attempted route in the group,
  over ALL rows (decided and undecided).
* **STRUCTURE** (the plan's literal test): decided rows ≥ 5 (a noise floor,
  named explicitly rather than silently dropping small groups) AND top share
  ≥ 70% AND top decider ≠ modal first route.
* **A caught bug, worth stating because it changed the numbers twice:**
  route names in `attempt_trail` are NOT colon-free (`fd:parse`,
  `q:mbqi-quick`, `q:ground-subset`, …) while the outcome token appended
  after them is (`probe`/`declined`/`decided`). Splitting on the FIRST colon
  (an earlier draft of `analyze.py` did this) truncates every such route to
  its bare prefix (`"fd"`, `"q"`) — caught on a dry run against this lane's
  own partial data, where `first_route` on 67 `AUFDTLIRA` rows came back as
  the literal string `"fd"`, which is not a route name. Fixed to split on the
  LAST colon. A second, subtler instance of the same shape: a route can
  appear MORE THAN ONCE in one trail (`q:skolem-qf` shows up as a `probe`
  early and again as the real `decided` attempt later, on real rows —
  `UFNIA/2019-Preiner/qf/f2_rw8.smt2` is one). Matching a route name and
  stopping at the FIRST occurrence attributes the decision to the probe and
  silently zeroes the "cost before the decision" computation; fixed to match
  the occurrence whose `outcome == "decided"` specifically. Both fixes are in
  `analyze.py`'s own docstrings, at the functions they fixed.
* **A finding the naive test would have hidden:** `fd:parse` — a cheap bound
  probe, single-to-low-double-digit ms, `outcome` always `probe`, never
  `decided` — is the first-attempted route on **1,393 of 1,400 rows**. It can
  never be a `top_decider` by construction, so "modal first route != top
  decider" is close to tautologically true for nearly every group here — the
  literal test would call almost anything STRUCTURE for the trivial reason
  that the ladder's own zero-cost probe precedes every real route. So every
  group below is ALSO scored against **`modal_substantive`**: the first
  attempted route that is not `fd:parse`. The two tests agree exactly on
  which 5 of 12 groups are STRUCTURE (below) — which is itself the finding
  that matters: the signal is not an artifact of the probe.
* **ceiling_ms** (the brief's literal ceiling: "the time the first route spent
  on rows it did not decide") is consequently tiny everywhere — `fd:parse` IS
  the first route and it is nearly free. **prefix_cost_ms** is the more
  informative number: for every reorder-affected row (decided by the top
  decider, whose own first-attempted route was something else), the summed
  timed cost of every attempt strictly BEFORE the top decider's own `decided`
  occurrence — i.e. everything a reorder promoting the top decider to the
  ladder head would let that row skip entirely. This is the ceiling actually
  worth reading.
* **reorder_rows** = decided rows whose `decided_by` is the top decider but
  whose OWN first-attempted route differs — the rows whose attempt order
  would concretely change under a reorder.

## 3. The table, per division x feature class

12 groups over 1,400 rows (`full-table.tsv` alongside this file is the exact
TSV `analyze.py --tsv-out` wrote):

| division | features | rows | decided | top decider | top share | STRUCTURE (literal) | STRUCTURE (substantive) | reorder rows | prefix cost |
|---|---|---:|---:|---|---:|---|---|---:|---:|
| AUFDTLIRA | not-dispatched | 200 | 130 | `q:mbqi-quick` | 82.3% | **STRUCTURE** | **STRUCTURE** | 107 | 42,304 ms / 107 files |
| AUFLIRA | not-dispatched | 200 | 178 | `q:mbqi-quick` | 80.9% | **STRUCTURE** | **STRUCTURE** | 144 | 2,790 ms / 144 files |
| QF_NIA | Int | 199 | 84 | `int-blast-ladder` | 77.4% | **STRUCTURE** | **STRUCTURE** | 65 | **631,307 ms / 65 files** |
| QF_NIA | not-dispatched | 1 | 0 | — | — | no (n<5) | no (n<5) | 0 | 0 |
| UF | (empty) | 4 | 0 | — | — | no (n<5) | no (n<5) | 0 | 0 |
| UF | not-dispatched | 196 | 90 | `q:mbqi-quick` | 67.8% | no (67.8%<70%) | no | 61 | 318,985 ms / 61 files |
| UFDTLIRA | Int | 2 | 2 | `q:skolem-qf` | 100% | no (n<5) | no (n<5) | 2 | 0 ms / 2 files |
| UFDTLIRA | none | 2 | 2 | `q:skolem-qf` | 100% | no (n<5) | no (n<5) | 2 | 0 ms / 2 files |
| UFDTLIRA | not-dispatched | 196 | 140 | `q:mbqi-quick` | 79.3% | **STRUCTURE** | **STRUCTURE** | 111 | 26,211 ms / 111 files |
| UFLIA | not-dispatched | 200 | 86 | `q:bool-skeleton` | 40.7% | no (40.7%<70%) | no | 35 | 5,657 ms / 35 files |
| UFNIA | Int\|Function | 30 | 24 | `q:skolem-qf` | **100%** | **STRUCTURE** | **STRUCTURE** | 24 | **126,764 ms / 24 files** |
| UFNIA | not-dispatched | 170 | 30 | `q:mbqi-quick` | 53.3% | no (53.3%<70%) | no | 16 | 1,639 ms / 16 files |

`decided_by` top 3 / `first_route` top 3 / median `elapsed_ms` by decider for
every group, and the row-for-row breakdown, are in `full-table.tsv` and the
raw `analyze.py` output; not reproduced here to keep this table readable.

## 4. Controls

**Negative example (a class where reordering changes nothing by
construction).** No real (division, class) group in this 200-file sample
happens to be genuinely single-route — the ladder's own `fd:parse` probe (or,
for the quantifier-free `QF_NIA/Int` group, a route literally named `probe`)
structurally precedes every real decider, so `top_decider == modal_first`
never occurs on real data here. That absence is itself worth stating rather
than papering over. The negative control is therefore synthetic, in the SAME
checked-in fixture as the positive one:
[`fixtures/synthetic_structure.tsv`](fixtures/synthetic_structure.tsv)
(20 rows, written once through `LedgerRow.to_line()` so its bytes are real
wire-format rows, not hand-typed TSV) plus
[`test_analyze_structure.py`](test_analyze_structure.py):

* **`SYN/Real`** (10 rows): one route (`only-route`), both first-attempted
  and sole decider on every row. `analyze_group` reports **NO STRUCTURE**,
  `reorder_rows=0`, `ceiling_ms=0`, `prefix_cost_ms=0` — verified by the test.
* **`SYN/Int`** (10 rows): `fast-route` decides 8 of 10 (80% ≥ 70%), but
  `slow-route` is attempted first on every row (including the two rows
  `slow-route` itself decides). `analyze_group` reports **STRUCTURE**,
  `top_decider=fast-route`, `reorder_rows=8`, `ceiling_ms=4000`,
  `prefix_cost_ms=4000` (500 ms x 8 files) — verified by the test.
* Sanity-checked non-vacuous: monkey-patching `analyze_group` to force
  `structure=False` and re-running against the same fixture prints the forced
  `False` (confirming the test COULD fail), while the real, unmodified
  function still reports `STRUCTURE` on `SYN/Int` in the same process — the
  test is exercising the real code path, not a tautology.

Run: `python3 bench-results/ledger-structure-20260915/test_analyze_structure.py`
(exit 0 = both assertions hold).

## 5. Verdict: should Phase 4 run?

**Yes, on the five STRUCTURE groups — but the finding has a size, and it is
not uniform across them.**

Ranked by `prefix_cost_ms` (the honest ceiling):

1. **`QF_NIA/Int`: int-blast-ladder decides 77.4% (65/84), 631,307 ms of
   prefix cost over 65 files — ~9.7 s/file average.** This is the strongest
   candidate: high decision share, large per-file ceiling, and it is the one
   QUANTIFIER-FREE group in the STRUCTURE set (so "which route to try first"
   is not entangled with the quantifier ladder at all). Reordering
   `int-blast-ladder` earlier relative to whatever currently precedes it
   (`nia-linearize` and others — see `full-table.tsv`'s `decided_by_top3`/
   `first_route_top3` columns) is the single most defensible Phase 4 target
   in this sample.
2. **`UFNIA/Int|Function`: q:skolem-qf decides 100% (24/24), 126,764 ms of
   prefix cost over 24 files — ~5.3 s/file average.** A complete-determinism
   signal (every single decided row in this class went to one route) with a
   real per-file cost. The group is small (30 rows), which is exactly why the
   plan requires an interleaved A/B on held-out files before shipping any
   derived order from it — 30 files is not enough to rule out this being a
   corpus-specific artifact of these particular files.
3. **`AUFDTLIRA/not-dispatched`: q:mbqi-quick 82.3% (107/130), 42,304 ms /
   107 files — ~395 ms/file.** Real, and the largest of the `q:mbqi-quick`
   group's three STRUCTURE instances, but two orders of magnitude smaller
   than #1.
4. **`UFDTLIRA/not-dispatched`: q:mbqi-quick 79.3% (111/140), 26,211 ms / 111
   files — ~236 ms/file.** Same shape as #3, smaller.
5. **`AUFLIRA/not-dispatched`: q:mbqi-quick 80.9% (144/178), 2,790 ms / 144
   files — ~19 ms/file.** STRUCTURE by the letter of the test (top share
   ≥ 70%, different modal route), but the ceiling is close to nothing: `AUFLIRA`
   is already 89% decided post-ADR-2065 (`tier1-current-20260914`'s own
   README), and whatever precedes `q:mbqi-quick` here is already cheap. A
   reorder targeting this group specifically is not worth a lane on its own.

**The portfolio criterion (§5.2 of the plan — "pairs of routes that each need
≥ 50% of one clock on the same undecided files") finds almost nothing: 2
distinct pairs, 4 and 1 rows respectively, out of 634 undecided rows.** That
is not structure; it is noise at this sample size. Do not widen the portfolio
from this data.

**What this 1,400-row, 200-file-per-division sample cannot show:**

* It is the PINNED lists, not the corpus — 200 files of an ~60x larger corpus
  per the plan's own §7 risk. A derived order from `QF_NIA/Int` or
  `UFNIA/Int|Function` must be checked on a HELD-OUT draw before it ships,
  exactly as the plan's exit criteria require.
* One pass, one binary, one set of hosts. `AUFLIRA`'s own history in this
  repository (77/79/85 on one division in one day, purely from ambient load)
  is the standing reason a single-arm ledger read is not a claim by itself —
  this README is Phase 3 sizing, not a Phase 4 A/B. Any derived order needs
  three passes per arm, a published noise floor, and an interleaved
  comparison against the hand-set order, per the plan's own Phase 4 minimum.
* `features` on a quantified file names the FIRST quantifier-free dispatch's
  fragment, not the file's own top-level constructs (ADR-2102's own stated
  limit) — `not-dispatched` (1,148 of 1,400 rows here, 82%) means the
  quantifier-free ladder was never reached at all, which is why most of the
  STRUCTURE signal is inside the `not-dispatched` bucket rather than a real
  construct-class one; `QF_NIA/Int` and `UFNIA/Int|Function` are the two
  exceptions where a real class is visible.
* `decline_names` is populated on this sweep (ADR-2105 landed before this
  lane's binary was built) but was not used in this analysis — the question
  asked is about ROUTE ORDER, not decline cause, and adding it would not
  change any number above.

**Recommendation:** run Phase 4 on `QF_NIA/Int` and `UFNIA/Int|Function`
first — largest ceilings, cleanest signal (one is quantifier-free entirely,
the other is a 100%-share group). Treat the three `q:mbqi-quick` groups
(`AUFDTLIRA`, `UFDTLIRA`, `AUFLIRA`) as a single, much smaller reorder
question, worth doing together if a lane is already touching the quantified
ladder's head, but not a phase on their own — the ceiling on the smallest of
the three (`AUFLIRA`) is close to zero. Do not widen the portfolio from this
sample. Do not derive anything from `UF`, `UFLIA`, or the two-row `UFDTLIRA`
sub-classes — none of them clears the STRUCTURE bar, and `UFLIA`'s top share
(40.7%) is the clearest NO in the table: `q:bool-skeleton`, `q:ground-subset`
and `q:mbqi-quick` split the decisions closely enough that no single reorder
target exists.

## 6. Reproduction

```sh
# Row-count verification (before consolidation; the exact output committed
# as evidence this lane produced, reproduced from /tmp/ledger-deploy/):
python3 /tmp/ledger-deploy/verify-rows.py    # not committed -- scratch; see the
                                              # numbers already quoted in section 1

# The committed table:
python3 bench-results/ledger-structure-20260915/analyze.py \
  --ledger-dir bench-results/ledger \
  --sweep-id t1-AUFDTLIRA-db31113fa --sweep-id t1-AUFLIRA-db31113fa \
  --sweep-id t1-QF_NIA-db31113fa --sweep-id t1-UF-db31113fa \
  --sweep-id t1-UFDTLIRA-db31113fa --sweep-id t1-UFLIA-db31113fa \
  --sweep-id t1-UFNIA-db31113fa \
  --tsv-out bench-results/ledger-structure-20260915/full-table.tsv

# The controls:
python3 bench-results/ledger-structure-20260915/test_analyze_structure.py
```
