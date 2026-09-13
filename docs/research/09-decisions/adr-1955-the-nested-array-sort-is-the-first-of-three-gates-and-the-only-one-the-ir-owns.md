# ADR-1955: the nested array sort is the first of three gates, and the only one the IR owns

Status: accepted
Index-summary: `ArraySortKey::Array(ArraySortId)` — an interned array-sort id behind the component key, leaving `Sort::Array { index, element }` and `Sort: Copy` untouched — is the right design and is NOT built yet. Measured over all 29,564 files of AUFLIRA/ABV/ALIA/AUFNIRA: the parse refusal blocks 27,150, but a FLAT `(Array Int Real)` read-over-write is already undecided, which rules out 19,620 of them on a second gate the IR does not own; the remaining 7,530 sit behind a third (nested `select` bases in `RowCtx::resolve_select`); the same divisions' 2,414 already-parsing files put the whole three-part chain at ~1,135 reachable files (4.2%), essentially all of them one family of ABV. The IR change alone decides zero files. The gate chain is pinned in `tests/nested_array_gate_map.rs`.
Index-status: accepted
Date: 2026-09-13

## Context

`crates/axeyum-ir/src/sort.rs` carries its own instruction:

> *"Nested arrays need an interned array-sort id before they become public
> surface."*

`Sort` is `#[derive(Copy)]`, so `Sort::Array` cannot hold recursive `Sort`
values without boxing; `ArraySortKey` is therefore a flat, non-recursive enum
and `ArraySortKey::from_sort` returns `None` for `Sort::Array` and `Sort::Seq`.
Four SMT-LIB divisions fail at ingest because of it, with one message:

    parse error: unsupported: nested array element sort is unsupported

This lane was dispatched at that refusal as **"the single largest mass behind
one decision"** — 29,564 files, AUFLIRA (20,011) first among them. It is the
largest mass. It is not behind one decision.

## What was measured

Everything below is over the **whole population** unless it says otherwise. The
only prior data on these four divisions was a 2–3 file per division sample in
`bench-results/session-20260911-smtlib/coverage/blockmap.txt`, a file carrying
its own `PARTLY REFUTED` banner (10 of its 13 re-measured rows were wrong).
Artifacts: [`bench-results/nested-array-ir-20260913/`](../../../bench-results/nested-array-ir-20260913/README.md).

### 1. The blocked count is 27,150, not 29,564

All 29,564 files through the real parser:

| division | files | parse ok | nested-array refusal |
|---|---:|---:|---:|
| AUFLIRA | 20,011 | 1,367 (6.8%) | **18,644** (93.2%) |
| ABV | 4,975 | 473 (9.5%) | **4,502** (90.5%) |
| ALIA | 3,098 | 70 (2.3%) | **3,028** (97.7%) |
| AUFNIRA | 1,480 | 504 (34.1%) | **976** (65.9%) |
| **total** | **29,564** | **2,414** (8.2%) | **27,150** (91.8%) |

`nested array element sort` is not the largest parse failure in these
divisions — it is the **only** one. Every division's histogram has exactly one
non-`ok` bucket.

A second, independent instrument agrees exactly. `census_nested.py` is a
textual s-expression scan sharing no code with the Rust parser (comment
stripping, 0-arity `define-sort` alias expansion): 18,644 / 4,502 / 3,028 / 976,
**identical in all four divisions**. Cross-checked on a fifth it was not tuned
on — AUFDTLIRA, 488 of 11,043 (4.4%) — against
[ADR-1927](adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)'s
5 of ~200 through the full ladder (expected 8.8 at p = 0.044; 1.4σ).

### 2. A FLAT array already fails for 19,620 of them

The nested shapes are one per division and unambiguous (n = 400 full-span each):

| division | dominant nested sort | leaf |
|---|---|---|
| AUFLIRA | `(Array Int (Array Int Real))` | **Real** |
| AUFNIRA | `(Array Int (Array Int Real))` | **Real** |
| ALIA | `(Array Int (Array Int Int))` | Int |
| ABV | `(Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64\|32\|8)))` | BV |

So take the leaf sorts and ask the smallest question that needs the array theory
rather than constant folding — the read-over-write obligation at a **symbolic**
index, `(not (= (select (store m i v) j) (ite (= i j) v (select m j))))`, which
is unsat for every element sort. **No nesting anywhere in these queries:**

| element sort | verdict |
|---|---|
| `(Array Int Int)` | **unsat** |
| `(Array (_ BitVec 64) (_ BitVec 64))` | **unsat** |
| `(Array Int Real)` | **unknown** |

`scalar_alia_auflia_arrays_supported` (`crates/axeyum-solver/src/auto.rs:6098`)
requires `!features.has_real`, so `dispatch_array_fast_paths` declines and the
query falls to the terminal non-BV array `Unknown` at `auto.rs:5405`. **AUFLIRA
and AUFNIRA's 19,620 nested files need a capability the IR does not own, and
lifting the parse refusal does not bring them one step closer to a verdict.**

### 3. The 7,530 that remain need a third gate too

ALIA and ABV are the half where nesting is the first binding gate. It is not the
last: `RowCtx::resolve_select` (`crates/axeyum-solver/src/abv.rs:2735`) has no
arm for an array-valued base that is itself a `Select`, so
`select(select(m,i),j)` reaches its catch-all and the query comes back as
`lazy-ROW declines` (`abv.rs:3562`). Behind that,
`is_warm_array_element_sort` (`incremental.rs:6014`) and
`finite_scalar_array_key` (`ufbv_online.rs:1745`) both admit only
`Bool | BitVec` elements.

### 4. What we decide in these divisions when parse is already behind us

The 2,414 files that parse today are the natural experiment: same divisions,
same solver, parse already behind them. At the board protocol — 24 s wall,
8 GiB, `taskset`-pinned core, `AXEYUM_TIMEOUT` 24,000 ms.

**A division's control is evidence about its blocked set only when the two come
from the same generator**, and in three of four divisions they do not. The
per-family rates, and how each family splits between the two populations:

| division / family | control files | decided | rate | blocked files from this family |
|---|---:|---:|---:|---:|
| **ABV** / UltimateAutomizer 2023 | 473 | 119 | **25.2%** | **4,502** |
| **ALIA** / UltimateAutomizer 2023 | 28 | 0 | **0.0%** | **3,028** |
| ALIA / piVC | 42 | 7 | 16.7% | 0 |
| AUFLIRA / `why` | 1,271 | (running) | ~61% at n=44 | 0 |
| AUFLIRA / `FFT` | 94 | 0 | 0.0% | 0 |
| AUFLIRA / `nasa` + `peter` | **0** | — | — | **18,644** |
| AUFNIRA / `FFT` | 470 | 1 | 0.2% | 0 |
| AUFNIRA / `nasa` | **0** | — | — | **976** |

Read the last column. **AUFLIRA and AUFNIRA have no control at all**: every one
of their 19,620 blocked files is `nasa`/`peter`, and not one `nasa` file parses.
Quoting either division's aggregate would have been actively misleading in both
directions — AUFLIRA's aggregate climbs toward `why`'s ~61%, a family that
contributes zero blocked files, while ALIA's 10.0% is **entirely** piVC, likewise
zero.

The mismatch is not incidental either. 100% of the `why`/`FFT` control declares
uninterpreted sorts and is refused for *that*
(`quantifier over non-enumerable domain (Uninterpreted 1)`,
`term #0 has sort (Uninterpreted 0) that the pure-Rust BV backend cannot
bit-blast`), while **0 of 300 sampled `nasa` files declare a sort at all**. The
control's blocker is not the blocked set's blocker, in either direction.

Two divisions do have a family-matched control, and they disagree with each
other: ABV decides **119 of 473 (25.2%)** of the same generator that produced
its 4,502 blocked files; ALIA decides **0 of 28**.

### 5. The reference cross-check on those decisions, and where it is vacuous

Every one of the 126 files ABV and ALIA decided was re-run against **z3 4.13.3**
and **cvc5 1.3.4** at the same budget on the same pinned core
(`z3 -T:24`, `cvc5 --tlimit=24000` — the units differ and mixing them corrupts a
board). No verdict contradicts a declared `:status` or another arm, in that run
or in the sweep behind it.

That is a weaker statement than it looks, and the weakness is worth publishing:

| | axeyum | z3 | cvc5 |
|---|---:|---:|---:|
| ALIA (7 decided) | 7 | **7** | **7** |
| ABV (119 decided) | 119 | **0** | **0** |

**On ABV the cross-check had zero opportunities to fire.** Neither reference
decides a single one of the 119 — they return `unknown` in about 0.1 s, and that
is the binaries' own behaviour, not the harness's (reproduced outside it). An
empty check is not a strong negative. The ALIA column is the part that is real:
three independent solvers, seven files, unanimous.

The incidental finding is on the same line: on the quantified-array shape these
SV-COMP files use, **we decide 119 files that neither reference decides**. One
was hand-checked and `sat` is correct for it: it asserts that no single store at
`~b~0.base` reaches `#valid`, which any `#valid` differing at a third index
satisfies.

For AUFLIRA and AUFNIRA there is no family-matched control at all, and the
mismatch is not incidental: 100% of the `why`/`FFT` control declares
uninterpreted sorts and is refused for *that*
(`quantifier over non-enumerable domain (Uninterpreted 1)`,
`term #0 has sort (Uninterpreted 0) that the pure-Rust BV backend cannot
bit-blast`), while **0 of 300 sampled `nasa` files declare a sort at all**. The
control's blocker is not the blocked set's blocker, in either direction.

## The design

Three options were sized before any was chosen. Blast radius is measured, not
estimated (`rg` counts across the workspace, `crates/axeyum-lean-*` excluded —
332 of the naive `: Sort` hits there are Lean's universe `Sort u` in doc
comments).

### Option A — `Sort::Array(ArraySortId)`

Replace the struct variant with an interned id. **254 `Sort::Array`
occurrences**, of which 83 are `{ .. }` wildcards that survive and **~170 bind
`index`/`element` by name** and do not. Rejected: it pays for recursion at every
site that only ever wanted the components.

### Option B — `ArraySortKey::Array(ArraySortId)` — CHOSEN DESIGN

Intern the *component* key, not the sort. `Sort::Array { index, element }` keeps
its shape, so all ~170 field-binding sites are untouched, and `Sort` stays
`Copy`: `ArraySortId(u32)` preserves `Copy + Hash + Eq` on `Op`, which matters
because `Op::ConstArray { index: ArraySortKey }` and `Op::SeqEmpty(ArraySortKey)`
are inside the hash-consing key `TermNode` (`crates/axeyum-ir/src/term.rs:78`).
**Interning does not force `Sort` non-`Copy`** — the hard rule in CLAUDE.md
about lifetime-free `Copy` handles is not in tension with this, and the exact
two-phase template already exists: `declare_datatype` / `add_constructor`
(`arena.rs:520`) buys datatype recursion the same way.

What breaks, and it is the honest cost:

| surface | count |
|---|---:|
| `ArraySortKey` mentions, 75 files (solver 333, ir 107) | 514 |
| `.to_sort()` — cannot expand a nested key without the arena | 46 |
| `ArraySortKey::from_sort` — cannot intern without `&mut` arena | 11 |
| `array_widths()` / `array_sorts()` | 8 / 8 |
| arena-aware renderers in `axeyum-smtlib/src/write.rs` | 3 |

The soundness property that makes this shape the right one: `Sort::array_sorts`
and `Sort::array_widths` already return `Option`, and every existing consumer
already handles `None` by refusing. A nested component returning `None` from the
arena-free helpers therefore keeps every route that cannot handle nesting
conservative **by construction** rather than by audit. The one place that must
NOT take that default is `Features::note_sort` (`auto.rs:10574`): it has to
recurse through the interned key or `has_non_bv_array` under-reports and the
query is mis-routed — a wrong-verdict path, not a decline. There is no serde
and no `FromStr for Sort`, so wire-format exposure is zero.

### Option C — curry the outer level, no IR change at all

`(Array I1 (Array I2 E))` is a function `I1 -> (Array I2 E)`, and this solver
**already decides array-valued uninterpreted function results** (ADR-0084/0092/
0093) — including a `store` into one. Blast radius: `axeyum-smtlib` only.

It was sized rather than assumed. Currying can express an outer occurrence in
`select` and `store` position and nothing else; over 600 full-span files per
division:

| division | curryable | positions blocking |
|---|---:|---|
| ALIA | **64.1%** | outer equality only (214 of 596) |
| ABV | **50.6%** | outer equality only (295 of 597) |
| AUFLIRA | **0.0%** | 593 of 600 quantify over an outer array **and** pass one as a function argument |
| AUFNIRA | **0.0%** | 600 of 600, same |

Rejected as the recommendation. It caps out around 4,200 files, cannot be
extended to the 19,620, and would be scaffolding thrown away when Option B
lands. The census instrument is kept, because the number is what makes the
rejection checkable.

## Decision

**Option B is the design. It is not built in this lane.**

The interned array-sort id is necessary for all 27,150 and sufficient for none
of them. Shipped alone it decides **zero files** while adding a 514-site
surface and one genuine mis-routing hazard. The chain is:

    parse refusal            27,150 files    IR   — this ADR's design
      +  nested select base   7,530 files    solver — abv.rs:2735, incremental.rs:6014
      +  Real-element arrays 19,620 files    solver — auto.rs:6098

and the third line is the one worth noticing: **it is the larger prize, it is
not blocked by the IR at all, and a flat array demonstrates it in one query.**
A lane can attack `!features.has_real` today without touching `Sort`.

Applying each division's **family-matched** control rate to its blocked count —
the only transfer the populations support — brackets the whole three-part chain
at

| division | blocked | family-matched control | reach |
|---|---:|---:|---:|
| ABV | 4,502 | **25.2%** (119/473) | **~1,135** |
| ALIA | 3,028 | **0.0%** (0/28) | **~0**; ≤ ~325 at the rule-of-three upper bound on 0/28 |
| AUFLIRA | 18,644 | none exists, and blocked by the Real gate | **~0** |
| AUFNIRA | 976 | none exists, and blocked by the Real gate | **~0** |
| **total** | **27,150** | | **~1,135, i.e. 4.2%** |

**Essentially all of the reachable population is one family of one division.**
That is the number to weigh 514 call sites and three capabilities against, and
it is still an over-estimate: it credits each division its control's rate, and
the nested files are the harder half of every one of them.

This is [ADR-1945](adr-1945-a-blocked-count-is-not-a-reachable-count-and-two-sequential-caps-are-not-two-caps.md)'s
rule applied *before* the build rather than after: a census attributing N files
to a blocker is an upper bound, and when the blockers are SEQUENTIAL GATES the
count attributed to the earliest is not reachable through it at all. Parse is
the earliest gate there is.

## Consequences

### What this buys

- Four divisions with no measurement of any kind now have pinned 200-file
  full-span lists, a whole-population parse census, and a first decide rate.
- **A free board row nobody was looking for.** AUFLIRA's `why` family — 1,271
  files, Why3-generated, no nested arrays, no board entry — decides at roughly
  61% on the sample run so far. It has nothing to do with this ADR's subject and
  was visible only because the control sweep was split by family.
- The next lane on this file is pointed at `auto.rs:6098`, not `sort.rs`.
- The gate chain is a test, not a memory:
  `crates/axeyum-solver/tests/nested_array_gate_map.rs`, seven tests, 0.11 s,
  named in `hooks/pre-push`. Three of them assert a capability we do **not**
  have and fail loudly when it arrives, saying which number in this ADR went
  stale. The `Int`/`Real` pair is its own control: the same query, one token
  different, opposite verdicts — so neither half can be vacuous.
  The Real case pins `Unknown` specifically rather than "not unsat", because
  the query is unsat by construction and a `sat` there would be a soundness
  defect rather than a frontier move.

### What it costs

Nothing is decided that was not decided before, and AUFLIRA stays at the top of
the file-count list with a 1.2% measured rate on the only part of it we can
read. A reader who wants the headline division moved has to accept that it needs
three capabilities, not one.

### What this ADR does not claim

- It does not claim Option B is hard. It is mechanical, and the two-phase
  datatype template is already in the arena.
- It does not claim the 6% bracket is a prediction of what Option B plus the two
  solver capabilities would deliver. It is an upper bound assembled from
  per-division control rates, two of which are family-mismatched and said so.
- It does not settle outer extensionality. 214 ALIA and 295 ABV files of 600 use
  outer array equality; whether a Skolem-index encoding decides them is
  unmeasured, and this ADR counts them as blocked rather than assuming either way.
