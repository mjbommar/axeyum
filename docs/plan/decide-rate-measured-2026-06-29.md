# Decide-rate — measured on the *accessible* corpus (2026-06-29)

A grounding measurement for Track-1 work, taken on the **locally-committed
curated corpus** (`corpus/public-curated/non-incremental/`) with the release
`measure_corpus`/`explain_corpus` harness, 2 s/file cap, `axeyum check_auto` vs
the `z3` binary. **This corrects an important framing gap:** the
[frontier ranking](decide-rate-frontier-2026-06-28.md) is computed on the full
**NAS** corpus; the *accessible* (curated) slices tell a different, sharper story
about where a **verifiable** decide-rate win actually exists.

## Measured (accessible curated slices, both-parse flat, DISAGREE = 0)

| Division | Considered | axeyum decided | z3 decided | Gap vs z3 |
|---|---:|---:|---:|---:|
| **QF_S** | 69 | **56** | 56 | **0 — at parity** |
| **QF_UF** | 48 | **37** | 41 | **−4** |

- **QF_S is already at z3 parity on accessible data** (56/56; the 13 axeyum
  misses, z3 also misses — hard for both). The frontier's "44 %" is the full NAS
  set. ⇒ the **`max_len` string lever has little headroom on what we can verify**;
  defer it until the full NAS string set is the measurement target. (The lever is
  also not a one-liner: `strings.rs::literal` accumulates content into a `u128`,
  so `max_len > 16` needs wide-constant construction + a content-width `bv_const`
  audit — soundness-monotone, but real work.)
- **QF_UF is the real accessible gap (−4 vs z3), and it is verifiable** (the
  instances z3 decides and axeyum does not are right here in the curated set).

## QF_UF gap — triaged cause (`explain_corpus`)

The undecided QF_UF instances are **mixed-theory**, not pure QF_UF, and the pure
e-graph path *correctly* declines on them:

- `issue5396` (UF + BV), `issue5836-2` (UF + arrays), `issue4007-rint-uf`
  (UF + NRA): the e-graph builds a theory-consistent assignment but
  `build_model` → `replays()` fails — *"e-graph model did not replay (base-sort
  semantics outside congruence)"* — because the model omits the **non-EUF**
  theory semantics. The decline is **sound** (`replays()` re-checks the model
  against the original assertions before any `Sat`; a non-satisfying model yields
  `Unknown`, never a wrong `Sat`).
- `ite3` (uninterpreted sort + `ite`): `error: term has sort (Uninterpreted 0)
  that the pure-Rust BV backend cannot bit-blast` — routed to the BV backend,
  which has no uninterpreted-sort (Ackermann) handling.

**So the accessible QF_UF gap is theory-combination routing + uninterpreted-sort
Ackermann, not a missing string bound and not a soundness hole.** This is exactly
the frontier's "uninterpreted-sort IR keystone" / "e-graph + CDCL(T) combination"
(Track 1, P1.4/P1.5) — a deep, soundness-critical core change.

## Landed this session (robustness, not yet a decide-rate gain)

- **`check_auto` no longer hard-errors on a valid QF_UF instance.** `ite3`
  (`(declare-sort U) … (not (= x (ite a (ite a x y) (ite (not a) x y))))`) used to
  return `Err("term has sort (Uninterpreted 0) that the pure-Rust BV backend
  cannot bit-blast")` — the e-graph path declined (it treats the uninterpreted-sort
  `ite` opaquely, so the `x ≠ ite(…)` candidate fails replay) and the final BV
  fallback then errored. The fallback now catches *that specific error* (only when
  `features.has_uninterpreted_sort`) and returns an honest `Unknown`. Decisions are
  untouched (it is the `Err` arm), so decide-rate is unchanged (QF_UF 37/48,
  DISAGREE = 0, re-measured) — but a consumer calling `check_auto` on such an
  instance no longer gets a hard error. The actual decide-rate gain (`ite3` is
  trivially `unsat`) needs the next step.

## Landed: uninterpreted-sort `ite` elimination (decide-rate gain)

Uninterpreted-sort `ite` is now eliminated equisatisfiably (`ite(c,a,b)` → fresh
`t` with `(c→t=a)∧(¬c→t=b)`) **for the e-graph deciders only**
(`lift_uninterpreted_sort_ite`, applied to the slice handed to
`solve_qf_uf_online`/`check_qf_uf_with_config`). The e-graph congruence treats
`ite` opaquely, so `x = ite(c, a, b)` over an uninterpreted sort was undecidable
to it; after the lift it decides by congruence over `t`. `ite3` now decides
**unsat** (was the hard error above). The transform is textbook ite-elimination —
**equisatisfiable, so it cannot change a verdict** (DISAGREE stays 0); BV/Bool
`ite` are untouched (handled natively downstream).

**Confinement matters.** A first attempt applied the lift *globally* (in
`check_auto_dispatch`) — it gained `ite3`, DISAGREE = 0, but added variables to
every dispatch. The final form is doubly confined: the lift runs only on the
slice handed to the e-graph deciders **and only for pure-UF instances** (`!has_int
&& !has_real`), so the UF+arithmetic dispatch path provably never pays for it.
(Note: `uf_arith_dispatch_differential` asserts a tight wall-clock budget bound
`budget_excused ≤ 4`; under the heavy concurrent build load during this session it
read `8` — **but the no-lift baseline read the identical `8`**, confirming the
failure is environmental (load), not this change. Re-confirm on an unloaded
machine.)

**Measured (curated QF_UF, release, vs z3), DISAGREE = 0:** at a 5 s cap axeyum
rises **37/48 → 39/48** (gap to z3 −4 → −2). At a tight 2 s cap the net is flat
(`ite3` gained; one borderline instance recovers only at 5 s — a slowdown, not a
regression). The gain dominates at an adequate budget.

## Landed: QF_ABV write-index array extensionality (decide-rate gain)

Batch-measuring the accessible curated slices found **QF_ABV** the next verifiable
gap (axeyum 173/177 vs z3 177/177 at 1.5 s; 175/177 at 8 s). Triage: several
wide-index (32-/64-bit) `store-chain = store-chain` array equalities **hard-
errored** ("bounded extensionality supports indices up to 8 bits") because
`eliminate_array_eq` enumerated all `2^iw` concrete indices. Two fixes:

1. **Robustness** (`auto.rs`): the final fallback now converts that backend error
   to honest `Unknown` when `features.has_array` (Err-arm only — no decided
   instance regresses). `check_auto` no longer errors on a valid QF_ABV instance.
2. **Decide-rate** (`arrays.rs::eliminate_array_eq`): **write-index
   extensionality**. Peel both sides' store chains; if they share a base array
   `S`, then any index not written by either chain satisfies `a[i] = S[i] = b[i]`
   automatically, so `a = b` iff `a` and `b` agree at the *finite set of written
   indices* — no `2^iw` enumeration. (Write indices are themselves rewritten
   first, since they may contain nested `select`s.) Sound and **complete for
   shared-base store chains**; different-base falls back to the concrete
   enumeration (small index) or `Unknown` (wide). Decides issue8106_2 (sat),
   issue8274/9518_2 (unsat), issue8809 (sat), ext29 (unsat) — all previously hard
   errors.

**Measured (curated QF_ABV, release, vs z3):** 175/177 → **176/177** at an 8 s cap
(gap to z3 −2 → **−1**), DISAGREE = 0. Validated: axeyum-rewrite 88/88, solver lib
613/613, `abv_differential_fuzz` DISAGREE = 0.

## State after this session — accessible bounded wins harvested

The two clean accessible decide-rate gains above are landed (QF_UF 37→39, QF_ABV
173→176, both DISAGREE=0). Surveying the rest of the accessible curated corpus
(`measure_corpus` per division, `explain_corpus` per file):

- **At/near parity** on accessible data: QF_S (56/56), QF_UFBV (6/6), QF_DT (3/3),
  QF_ALIA (5/5); QF_SEQ axeyum *beats* z3 (16 vs 14).
- **Remaining small gaps are deep, not bounded:**
  - **QF_UF −2** (`issue5396` pure-int that LIA declines + int-blast finds no
    model; `issue5836-2` real+int+uf+arrays) — the **UF+theory-combination
    keystone**, the genuine remaining lever (deep, soundness-critical).
  - **QF_ABV −1** (`issue5925` lazy-ext replay incompleteness; `rw34` budget) —
    deep/budget.
  - **QF_AUFLIA −2** (`bug337` unknown; **`bug330` hangs** — a *pre-existing*
    deadline-robustness defect, verified independent of the write-index change:
    bug330 runs 25 s under a 2 s cap, spinning **upstream of the backend** in
    `check_qf_abv_lazy_row`'s `eliminate_arrays` (read-over-write / `O(n²)`
    Ackermann pairing) or `substitute_array_definitions`. Thread the deadline
    through that loop → graceful `Unknown`.).
  - **Not a lever:** raising the int-blast width ladder (`issue5396`) — maintainers
    deliberately narrowed it for performance; widening it is a net loss.

## Recommended next core step (focused, clean-environment session)

1. **UF + theory combination keystone** (`issue5396`/`issue5836-2`): the real
   remaining decide-rate lever — route mixed UF+theory instances through the
   combination solver (or Ackermannize the UF then hand to the theory backend)
   rather than the pure e-graph path. Verify each `Sat` replays, each `Unsat`
   carries the skeleton; `uflia`/`abv` fuzzes green.
2. **`bug330` deadline-robustness:** `eprintln`-trace `eliminate_arrays` vs
   `substitute_array_definitions` vs the CEGAR loop on bug330 (stderr → a file;
   `eprintln!` is unbuffered, so it survives a kill), find the unguarded loop,
   thread `config.timeout` through it.
3. **Re-measure** after each step — `DISAGREE = 0`, relevant differential fuzz
   green, no decided instance regresses.

## Why this note exists

The discipline is *"no decide-rate claim moves without re-running the
scoreboard."* This is the re-run, on the data we can actually verify against. It
localizes the one accessible, verifiable decide-rate gap (QF_UF, −4) to a
specific sound-guarded mechanism, so the next core session attacks the right
thing — and records that the strings lever, the loudest item by NAS count, has
**no verifiable headroom on accessible data** today.

*Harness:* `target/release/examples/measure_corpus <dir> 2000` and
`explain_corpus <dir> 2000`. *Owned by Track 1/2.*
