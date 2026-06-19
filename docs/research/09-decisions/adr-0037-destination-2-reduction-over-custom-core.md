# ADR-0037: Destination-2 priority is word-level reduction, not a custom default SAT core

Status: accepted
Date: 2026-06-18

## Context

Destination-2 (Z3-class measured speed) is the standing open gap: on the committed
113-file public QF_BV slice (`20221214-p4dfa-XiaoqiChen`, SMT-LIB 2024 / Zenodo
11061097) axeyum's eager bit-blast path decides **~2–3 / 113** at second-scale
budgets while Z3 sweeps essentially all of them. Two candidate levers had to be
disambiguated by measurement before pouring effort into either:

1. **Lazy/word-level bit-blasting (`LazyBvBackend`, CEGAR over heavy arithmetic).**
2. **A competitive custom SAT core** (the modernized `proof_sat` / `xor_cdcl` with
   VSIDS/Luby/LBD) replacing `rustsat-batsat` on the default path.

A prior note hypothesized lazy-bv as "THE lever." This ADR records the measured
reality and picks the destination-2 direction explicitly, per the project rule that
performance-strategy decisions are not made silently in code.

## Evidence (fair, committed, public-slice measurements — 2026-06-18)

All runs: same node/CNF budgets as the committed eager `qf-bv-p4dfa-fair` baselines,
Z3 4.13.3 oracle, `--jobs 2`, `DISAGREE=0` and `0` model-replay failures throughout.

- **lazy-bv is structurally inert on this corpus.** Fair runs decided 3/113 @3s and
  4/113 @20s, but `lazy_ops_total == 0` on **all 113** files and **0** ops were ever
  refined — an operator census confirms **0/113** files contain *any* heavy
  arithmetic op (`bvmul`/`bvudiv`/`bvsdiv`/`bvurem`/`bvsrem`/`bvsmod`). Every decided
  instance was plain bit-blast; the +1 over eager is a solve-path margin, not a CEGAR
  win. The slice is arithmetic-free DFA/protocol bit-logic (`bvadd`/`bvand`/`bvxor`
  over wide vectors, huge `ite`-nests). Lazy arithmetic-CEGAR has nothing to abstract
  here. (It remains the right tool for arithmetic-heavy corpora — see the curated
  multiplier slice — so it is kept, not removed.)
- **The wall is eager-CNF size, attacked directly by reduction.** The ~110 unknowns
  are ~87–98 Timeout (admitted, bit-blasted to CNFs batsat can't crack in budget) +
  ~10–13 **EncodingBudget** (refused *before* solving — too large to even encode) +
  ~1–10 NodeBudget. Word-level preprocessing — once made scale-safe (see below) —
  decided **4 / 113 vs eager's 2** at the same 3s budget, with PAR-2 non-worse
  (5.84 vs 5.90). The mechanism is exactly the predicted one: the two newly-decided
  instances **drop out of `EncodingBudget` (13 → 11)** because `solve_eqs` +
  canonicalize shrink them below the bit-blast-size ceiling.
- **Reduction was previously unusable at scale; that is now fixed.** Profiling the
  17.6 MB / 340 k-node giant showed `solve_eqs` was the sole hog (**>150 s** there;
  every other pass <0.5 s) — its `O(eliminations × surviving-nodes)` substitution
  loop ran effectively unbounded. A deterministic node-fuel budget
  (`solve_eqs_bounded` / `DEFAULT_SOLVE_EQS_FUEL`, commit `96e55b6`) bails to a sound
  partial reduction; the giant now clears the whole pipeline in ~1.5 s.

Baselines:
`bench-results/baselines/qf-bv-p4dfa-fair-{lazy-bv,sat-bv-preprocess}-vs-z3-*.json`.

## Decision

1. **The destination-2 priority for the bit-blast path is word-level *reduction*
   ("not-building-the-mountain"), not replacing the default SAT core.** Effort goes
   to P1.2 (word-level preprocessing: `solve_eqs`, `propagate_values`,
   `elim_unconstrained`, AC/`ite` simplification, max-sharing) and to broadening
   reduction toward what Z3 does at the word level. This is what the public number
   responds to (the encoding ceiling is the binding constraint, and reduction is the
   only lever that both shrinks the CNF *and* pulls instances below the encoding
   ceiling).

2. **`rustsat-batsat` stays the default clausal engine.** The modernized custom cores
   (`proof_sat` — DRAT/1-UIP/VSIDS; `xor_cdcl` — XOR-dense) remain *specialized*
   (proof production, GF(2)-structured corpora), not the default QF_BV path. A faster
   SAT core only attacks the Timeout subset and would still face million-clause
   structural CNFs that Z3 never builds; it is the wrong place to spend first. This
   does **not** abandon the custom-core identity (ADR-0002) — it sequences it after
   reduction.

3. **Reconsideration trigger — PARTIALLY FIRED by measurement (2026-06-18).** The
   trigger was: revisit "make a custom core the default path" when a corpus shows the
   still-undecided instances are **SAT-search-bound**. A direct kissat-4.0.4 probe of
   the 99 public Timeouts (bit-blast to DIMACS, run a state-of-the-art core on what
   batsat times out on) shows this **is true for the small-CNF subset**: kissat solves
   every Timeout ≤ ~300 k clauses (2–18 s; `mobiledevice_paired` 2 s vs batsat > 20 s)
   — **~9 of 99 are SAT-search-bound**. The larger ~90 (≥ ~650 k clauses) defeat even
   kissat in 30 s and remain reduction-bound. **Consequence:** a competitive default
   SAT core (P1.3 — VSIDS/restarts/LBD, already prototyped in `xor_cdcl`) is now a
   *data-justified* lever for the small-CNF Timeout band, complementary to reduction
   (which leads for the large-CNF bulk + `EncodingBudget` set). The "reduction first"
   priority stands for the bulk; the core work is no longer purely deferred — it has
   an earned, measured target. (See the kissat table in
   [lazy-bitblasting-p21-findings.md](../05-algorithms/lazy-bitblasting-p21-findings.md).)

4. **Word-level preprocessing moves toward default-on (extends ADR-0034).** The public
   measurement **meets ADR-0034's own ratification criterion** for flipping the
   default (net non-negative decided delta + non-worse PAR-2 + `DISAGREE=0` + 0 replay
   failures on the public corpus). **Implementation gap to close first (not silently):**
   the default `solve()`/`check_auto` path currently honors `config.preprocess` by
   running **canonicalization only** — *not* the full model-sound pipeline
   (`propagate_values` → `solve_eqs_bounded` → `elim_unconstrained`) that produced the
   measured win in `check_with_preprocessing` / the bench `--preprocess` path. So the
   concrete next step is to route the full pipeline (with trail-based model
   reconstruction + original-assertion replay) into the default path, re-run the
   curated + public baselines, and only then flip `SolverConfig::preprocess` to
   default-on in a follow-up. Until then the win is reachable via
   `check_with_preprocessing` and `--preprocess`, both sound and scale-safe.

## Consequences

- Destination-2 work is now pointed at reduction breadth (the measured lever), with a
  concrete, sound, scale-safe foundation (`solve_eqs_bounded`) and a measured +2/113
  to build on.
- The custom SAT cores are not wasted — they are sequenced behind reduction and remain
  the lever for the arithmetic/SAT-search-bound regime (curated slice, ADR-0035).
- A small, honest implementation gap (full preprocessing on the default path) is
  recorded as the next step rather than left as a silent flag-vs-behavior mismatch.

## Alternatives considered

- **Flip `preprocess` default-on now (one-line).** Rejected: the default path only
  canonicalizes, so the flip would *not* reproduce the measured win and would change
  every baseline for little gain. Route the full pipeline first.
- **Invest in a competitive default SAT core now.** Rejected for this corpus: the
  binding constraint is encoding size (EncodingBudget refusals + huge CNFs), which a
  faster core does not address; Z3's advantage here is word-level reasoning, not a
  faster SAT backend.
