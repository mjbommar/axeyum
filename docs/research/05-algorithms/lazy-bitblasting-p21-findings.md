# Lazy bit-blasting (P2.1) — measured findings and the wiring plan

Status: **measurement-grounded design note (2026-06-17).** Records what the
existing-but-unwired lazy bit-blasting lever actually does, so the next
performance step (wiring + broad measurement) is executed cleanly, coordinated,
and gated on `DISAGREE=0`. This is destination-2 (Z3-class measured speed), the
biggest open gap: axeyum decides **~2–3 of 113** real public QF_BV problems Z3
sweeps in ~1 s each, because the **default path eagerly bit-blasts everything** to
a ~1M-clause "switch-mountain" the SAT solver drowns in.

## The key fact: the lever exists, and it's NOT wired in

`solve_lazy_bv_abstraction` (`axeyum-solver/src/lazy_bv.rs`, ADR-0019) already
implements abstraction-refinement (CEGAR) bit-blasting: it abstracts every heavy
gadget (`bvmul`/`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`) by a fresh
unconstrained variable (a sound over-approximation), solves the much smaller
abstraction with the eager path, and — on a spurious `sat` — refines only the ops
whose abstraction value disagrees with their real result (bit-blasting *just
those*), re-solving to a fixpoint. Sound, complete, terminating; every `sat`
replays; `unsat` is sound by over-approximation.

**But `grep` of `auto.rs`/`backend.rs` finds no call to it — it is built but never
invoked by the default `solve()`/`check_auto` or the bench.** So the "2–3/113"
number is the eager mountain-builder; the lever that sidesteps the mountain sits
unused.

## What it actually does (measured — `tests/lazy_bv_curated_measure.rs`)

| cohort | instance | result | heavy ops blasted |
|---|---|---|---|
| **incidental** | `x=1 ∧ x=2 ∧ r=p·q` (64-bit `bvmul`) | lazy **unsat ~0 ms** (eager 17 ms) | **0 refined** — multiplier never materialized |
| **essential** | curated `mulhs08`/`stp_samples` (multiplier IS the crux) | lazy refines all → still unknown | no shortcut (= eager) |
| **selective** | curated `calypto_9` | lazy **sat in 923 ms** | only **2** of its ops refined |
| **no-op safety** | 2 small public files (no heavy ops) | lazy = eager (5 vs 8 ms; 86 vs 90 ms) | `ops=0` — zero overhead |

Reading: lazy is a decisive win when the heavy op is **incidental** (the
contradiction/model lives in non-multiplier constraints) — it decides *without
building the mountain*; it is a safe no-op when there are no heavy ops; it offers
no shortcut on pure multiplier-*equivalence* (those genuinely need the multiplier
— that's the CDCL(XOR)/algebraic frontier). The broad public QF_BV families here
(Composition/MobileDevice/StringMatching/TCP/VideoConf — software/protocol
verification) are exactly the incidental-heavy-op regime where this should move
the scoreboard, and where Z3's word-level reasoning wins today.

## The wiring plan (the high-ROL next step — likely a real jump, no new algorithm)

**Status update (2026-06-17): step 3's opt-in dispatch landed** in commit
`10a412e`. `SolverConfig::lazy_bv` (off by default) + `with_lazy_bv` route the
quantifier-free path through `solve_lazy_bv_abstraction`; the hook is
recursion-safe (inner abstraction solves run with the flag cleared) and a safe
no-op when no heavy ops are present. Verified by `tests/lazy_bv_dispatch.rs`
(routes-and-decides incidental UNSAT with 0 ops materialized; flag-off unchanged;
lazy agrees with eager on a sat model needing the heavy op). The remaining work is
the *measurement* path (steps 1–2) and the default-on decision (the tail of 3).

1. **Make it measurable (bench backend) — blocked on an arena-mutability
   impedance.** `solve_lazy_bv_abstraction` takes `arena: &mut TermArena` (it adds
   fresh abstraction symbols to the arena), but `SolverBackend::check` exposes only
   `&TermArena` and the whole bench pipeline (`solve_planned`, oracle compare,
   preprocessing) is built around the immutable-arena trait. So a drop-in
   `BackendKind::LazyBv` that just calls `solve_lazy_bv_abstraction` does **not**
   typecheck. Two clean resolutions, to be chosen in its own turn (not hacked into
   the shared `axeyum-bench/src/main.rs` mid-flight):
   - **(a) read-only entry point.** Add `check_lazy_bv_abstraction_ro(arena:
     &TermArena, …)` that copies the queried terms into a scratch `TermArena`, runs
     the existing mutable strategy there, and lifts the model back over the original
     symbols. Self-contained in `lazy_bv.rs` (not shared); the bench backend then
     fits the trait unchanged. Cost: a cross-arena term/model copy with its own
     replay test.
   - **(b) mutable-arena bench branch.** Special-case the lazy kind in `run_one`
     (which owns `mut script.arena`) to call `solve_lazy_bv_abstraction` directly,
     bypassing the `&TermArena` trait path. Smaller code, but forks the bench's
     solve/replay/oracle plumbing for one backend — more shared-file churn.
   Prefer (a): it keeps the bench's single solve path and the trait honest. Either
   way: additive edits only, commit promptly, no crate-wide fmt / destructive git
   (see the clobber post-mortem).
2. **Measure the public 113** (the big files need the bench's parallelism + memory
   caps; standalone harness only handles the 2 small ones). Headline metric: lazy
   decided-count vs the eager 2–3, with `DISAGREE=0` / 0 replay-failures the hard
   invariant. Record the per-family delta + `ops_refined` distribution.
3. **Wire into the product as a strategy.** `SolverConfig::lazy_bv` (opt-in first
   — **done**, `10a412e`), routed in dispatch when QF_BV carries heavy ops; next, a
   portfolio/strategy (try lazy when heavy ops present, eager otherwise). Default-on
   only after the public measurement (step 2) shows net benefit (an ADR, like
   ADR-0034 for word-level preprocessing default).
4. **Then deepen P2.1:** abstract *any* expensive subterm (not just mul/div),
   smarter refinement (refine the fewest ops), word-level slicing/sharing (P1.2)
   to shrink before abstracting, and P1.3 (competitive CDCL) for the bits that do
   get blasted.

## Measured on the public 113 (2026-06-17): the slice has NO heavy arithmetic — lazy is a measured no-op here

Steps 1–2 are now done: `BackendKind::LazyBv` (`f6cb39c`) ran the lazy backend
over the full 113-file public slice (`just bench-public-qfbv-lazy-vs-z3`'s
no-budget config, 1 s/file). Result:

```
lazy-bv:        files=113 sat=2 unsat=0 unknown=111 DISAGREE=0 replay_failures=0
eager (n1000):  files=113 sat=1 unsat=0 unknown=112 DISAGREE=0   (committed baseline)
```

**The hypothesis above was falsified by measurement.** Per-file telemetry shows
`lazy_ops_total == 0` for **all 113 files** — the slice contains *none* of the
six heavy arithmetic gadgets (`bvmul`/`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/
`bvsmod`) the abstraction targets, so `solve_lazy_bv_abstraction` falls straight
through to the eager path on every file. Lazy-bv **is** eager here; the 2 decided
are the two trivially-eager files. Confirmed across every family by operator
census:

| family | heavy-arith ops | `ite` count | size |
|---|---|---|---|
| Composition | **0** | 40 338 | 3.2 MB |
| MobileDevice | **0** | 2 850 | 270 KB |
| StringMatching | **0** | 25 730 | 2.0 MB |
| TCP | **0** | 6 972 | 690 KB |
| VideoConf | **0** | 7 968 | 715 KB |

So the bottleneck on this corpus is **formula size/structure** — gigantic
`ite`-nests plus `bvadd`/`bvsub`/`bvxor`/`bvand`/`bvor`/`distinct` blasting over
many variables — **not** the multiplier mountain. The eager CNF drowns the SAT
solver by sheer width, and arithmetic-CEGAR has nothing to abstract.

### What this redirects (destination-2 lever, corrected)

The lazy infrastructure is **correct, sound, committed, and the right tool for
arithmetic-heavy corpora** (the curated multiplier slice, crypto/SMT-COMP BV
families) — it is *not wasted*. It is simply **not the lever for this
ite/size-bound public slice.** The measured next levers, in priority order:

1. **`ite` / word-level reasoning** — `ite` is the dominant op (40 k in one
   file). Word-level `ite`-chain simplification and selective/shared blasting,
   not per-bit mux explosion, is where the size lives.
2. **P1.2 word-level preprocessing on this slice** — measure the committed
   `--preprocess` (AC-tree normalization) decided-count here; shrink before
   blasting. This is the already-built knob whose effect on *these* files is
   now the open question.
3. **Broader abstraction (the real P2.1 step 4)** — abstract *any* expensive
   subterm (wide `ite`-nests, adder chains, `distinct` cliques), not just the
   six arithmetic gadgets. The CEGAR machinery generalizes; the heavy-op set
   does not.
4. **P1.3 competitive CDCL** — for the large-but-arithmetic-free CNFs these
   produce, raw SAT throughput (VSIDS/restarts/LBD already landed for XOR) is
   the floor.

## The corrected lever's first blocker: the word-level preprocessor is unbounded (2026-06-17)

Acting on lever #2 (measure `--preprocess` on these 113) immediately hit a wall
that is itself the finding. Single-file timing under a hard OS cap:

| file | size | `ite` | `--preprocess` |
|---|---|---|---|
| `mobiledevice_…_twocond` | 270 KB | 2 850 | completes < 45 s |
| `compose.p2._…_paired` | 1.0 MB | 13 446 | completes < 60 s |
| `compose.s4._…_paired` | **17.6 MB** | **215 784** | **> 90 s — killed** |

The slice ranges up to a **17.6 MB / 215 k-`ite`** file; `--preprocess` has **no
time/work/fuel budget** (`grep` of `preprocess.rs` finds none), so on the giant
ite-DAGs it runs unboundedly. A `--jobs 8` run schedules several giants at once
and never finishes (observed: 14 small-family files ground 34 min with no
output). The non-preprocess path completes on the same files, so the blow-up is
*in preprocessing*, and — since canonicalization also runs in the non-preprocess
path — the suspect is **`solve_eqs`’ raw structural rebuild** (its own code
comment warns it inlines `x := t` by structural rebuild; on a heavily-shared DAG
that expands sharing toward an exponential tree).

**Next concrete code increment (Track 1):** give the preprocessing pass a
*deterministic* work budget (node-count / step fuel, not wall-clock — determinism
rule) so it bails to the un-reduced (or partially-reduced) problem instead of
hanging, and/or make `solve_eqs` sharing-preserving. Only then is word-level
reduction a measurable, shippable lever on this corpus. Until then `--preprocess`
is unusable at this scale.

## Lever #3 tested too: abstracting `ite` is sound but MEASURED INEFFECTIVE here (2026-06-17)

Broadened the lazy abstraction to BV-sorted `ite` (`SolverConfig::lazy_bv_abstract_ite`,
`LazyBvBackend::with_abstract_ite`, bench `--backend lazy-bv-ite`; commit
`5b7a82d` + the backend/bench variant). Sound (same over-approximation; UNSAT
sound, SAT replay-checked) and verified by unit tests. Measured on a small
MobileDevice file (270 KB, 2 850 `ite`), no node budget, 5 s:

```
sat-bv (eager):  unknown
lazy-bv-ite:     unknown   — ite_total=1254  ite_refined=1213 (97%)  rounds=4
```

**The `ite`s are essential, not incidental.** The abstraction refined **97 %** of
them (the candidate models violate nearly every abstracted `ite` — unsurprising
for control-flow verification, where the `ite` nest *is* the logic), so after
refinement the problem collapses back to the full eager circuit and still times
out. Same shape as essential multipliers: CEGAR only wins when the heavy op is
*incidental* to the verdict, and on this corpus neither arithmetic (absent) nor
`ite` (essential) is incidental.

The `ite`-abstraction code stays (sound, tested, and the right tool for a corpus
with *incidental* `ite`s), but it is **not** the destination-2 lever for this
software-verification slice. That leaves **word-level simplification** — shrinking
the `ite`/adder structure before blasting, as Z3 does — i.e. the (currently
unbounded) preprocessor, owned in `axeyum-rewrite`. Abstraction is exhausted as a
lever here; the remaining lever is reduction.

## Fair-budget re-measurement (2026-06-18): apples-to-apples vs the eager fair baselines

The earlier public measurement (above) used the no-budget 1 s config. This is the
**fair re-run at the same standing node/CNF budgets and timeouts as the committed
eager `qf-bv-p4dfa-fair-sat-bv-vs-z3-*` baselines**, so lazy-bv and eager sat-bv
are compared on identical terms. Backend `lazy-bv`, `--compare-z3` (Z3 4.13.3),
`--jobs 2`, on all 113 files.

| run | budgets | lazy-bv decided | eager sat-bv decided (baseline) | DISAGREE | replay fail |
|---|---|---|---|---|---|
| **3 s** | node 200k, cnf-var 2M, cnf-clause 5M | **3 sat / 110 unknown** (PAR-2 5.84) | 2 sat / 111 unknown | **0** | 0 |
| **20 s** | node 300k, cnf-var 3M, cnf-clause 8M | **4 sat / 109 unknown** (PAR-2 38.58) | 3 sat / 110 unknown (PAR-2 39.02) | **0** | 0 |

Baselines committed at
`bench-results/baselines/qf-bv-p4dfa-fair-lazy-bv-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`.

**The fair budgets confirm the no-op finding decisively.** Per-instance telemetry:
`lazy_ops_total == 0` on **all 113 files** (re-confirmed by an operator census —
`grep` finds **0/113** files containing any of `bvmul`/`bvudiv`/`bvsdiv`/`bvurem`/
`bvsrem`/`bvsmod`); **0 instances refined a single op**; every decided instance had
`ops_total = 0` (i.e. plain bit-blast, the abstraction was inert). The 110
unknowns break down (3 s) as **87 Timeout** (admitted, bit-blasted to large CNFs
batsat can't crack) + **13 EncodingBudget** + **10 NodeBudget** (refused at the
gate); at 20 s the bigger budgets shift it to **98 Timeout / 10 EncodingBudget /
1 NodeBudget**. The extra instances lazy decides over eager (`mobiledevice_…na6_nr3`
at 3 s, `compose.p2._…na6_nr3_paired` at 20 s) all have `ops_total = 0` and are
decided by the plain bit-blast path, not by CEGAR — a solve-path margin, within
noise, not an architectural win.

**Conclusion (the number the user asked for): lazy-bv does not — and on this
corpus structurally cannot — move the public QF_BV scoreboard.** The p4dfa slice is
arithmetic-free DFA/protocol bit-logic (`bvadd`/`bvand`/`bvxor` over wide vectors,
huge `ite`-nests); lazy arithmetic-CEGAR has nothing to abstract. The destination-2
wall on *this* corpus is **eager-bit-blast CNF size**, addressable only by
**word-level reduction before blasting** — which is gated on the **unbounded
preprocessor** (the `solve_eqs`/canonicalize blow-up on the 17.6 MB / 215k-`ite`
giants, recorded above). That blocker — a deterministic work budget on the
preprocessing passes — is the next concrete destination-2 code increment, not more
abstraction machinery.

## The corrected lever, unblocked and measured (2026-06-18): word-level preprocessing **doubles** the eager decided count

The unbounded-preprocessor blocker (above) is fixed: `solve_eqs` — measured as the
sole hog (the 17.6 MB / 340 k-node giant spent **>150 s** there while every other
pass finished in <0.5 s) — now takes a **deterministic node-fuel budget**
(`solve_eqs_bounded` / `DEFAULT_SOLVE_EQS_FUEL`, commit `96e55b6`) and bails to a
sound *partial* reduction (un-eliminated equalities stay ordinary assertions; the
trail still reconstructs). The giant now clears the whole pipeline in ~1.5 s.

With the preprocessor usable at scale, the fair `--preprocess` measurement (sat-bv
backend, **identical budgets to the eager fair 3 s baseline**, Z3 4.13.3 oracle,
`--jobs 2`):

| run | budgets | eager decided | **`--preprocess` decided** | DISAGREE | replay fail | PAR-2 (pp vs eager) |
|---|---|---|---|---|---|---|
| 3 s | node 200k, cnf 2M/5M | 2 sat | **4 sat** (EncodingBudget 13→11) | 0 | 0 | 5.84 vs 5.90 |
| 20 s | node 300k, cnf 3M/8M | 3 sat | **7 sat** | 0 | 0 | 37.89 vs 39.02 |

Baselines: `bench-results/baselines/qf-bv-p4dfa-fair-sat-bv-preprocess-vs-z3-{3s-n200k-cnf5M,20s-n300k-cnf8M}.json`
(`just bench-public-qfbv-preprocess-fair-{3s,20s}`).

**Word-level preprocessing genuinely moves the public number (2 → 4 at 3 s, and
3 → 7 at 20 s — more than doubling eager at both budgets, the gain *growing* with
the budget as reduced-but-still-hard formulas come into reach), and the mechanism
is exactly the predicted one:** the newly-decided 3 s
instances (`compose.p2._…na6_nr3_paired`, `mobiledevice_…na6_nr3_twocond`) are the
two that drop *out of* `EncodingBudget` (13 → 11) — `solve_eqs`/canonicalize shrink
them below the bit-blast-size ceiling so they encode and solve where the eager path
refused them. DISAGREE=0, 0 replay failures (the partial-reduction trail
reconstructs soundly). This is the first measured destination-2 gain on this corpus
from *reduction* rather than abstraction — confirming the "not-building-the-mountain"
direction over arithmetic-CEGAR (inert here) and over a faster SAT core (which would
only climb the same mountain). Full parity still needs far deeper word-level
reasoning (Z3 decides ~113), but the lever is now real, sound, scale-safe, and
pointed the right way.

## Where the win came from, and the next lever (2026-06-18)

The 20 s unknown breakdown isolates exactly what reduction did and what is left:

| reason | eager 20 s | `--preprocess` 20 s | change |
|---|---|---|---|
| Timeout | 99 | 99 | **0** |
| EncodingBudget | 10 | **6** | **−4** |
| NodeBudget | 1 | 1 | 0 |
| **decided** | **3** | **7** | **+4** |

**The entire +4 is the `EncodingBudget` → decided transition** — preprocessing
shrank 4 instances below the bit-blast-size ceiling so they encoded and solved. The
**99 Timeouts are untouched**: those encode fine either way, and the reduced CNF
still drowns the SAT solver in 20 s. So the two remaining levers, precisely scoped:

1. **6 still-`EncodingBudget` instances** — too big to encode *even after* the
   current reduction. **Diagnosed (2026-06-18):** all 6 are the `string4x16_bit16`
   family, and a term-level op census of the closest one (`string4x16.4`, est.
   3.1 M vars vs the 3 M budget — only ~3 % over) shows it is **overwhelmingly
   `ite`-driven: 129 870 `ite` over 16-bit vectors** (6× the next op; 9 548
   `BitVec(16)` vars, plus ~19 k each `bvadd`/`bvsub`, 22 k `=`, 9 k each
   `bvand`/`bvor`/`bvxor`). Each 16-bit `ite` bit-blasts to ~16 muxes, so the ~130 k
   `ite`s *are* the multi-million-clause encoding. The **basic `ite` rules already
   exist and ran** in this `--preprocess` measurement (`ite.const_condition`,
   `ite.same_branches`, `ite.bool_identity` in `canonical.rs`) — so the survivors are
   *genuine distinct-branch, symbolic-condition 3-way muxes*, not low-hanging
   redundancy. The remaining lever is therefore **deeper `ite`-aware reduction/
   encoding**: nested same-condition collapse (`ite(c, ite(c,x,y), z) → ite(c,x,z)`,
   common in string/automaton branching on a repeated character test), shared-mux
   encoding, and `ite`-lifting — *not* abstraction (the prior lazy-`ite` measurement
   found ~97 % essential, so CEGAR collapses to eager). A ~3 % encoding cut decides
   `string4x16.4`; larger cuts reach the rest. This is the precise next
   destination-2 effort (a focused `axeyum-rewrite`/encoding project), now scoped.
2. **99 Timeouts (the bulk)** — encode but don't solve. These need either *much*
   deeper reduction (shrink the CNF itself, the Z3 route) or, secondarily, a
   stronger SAT search on the blasted residue. Per ADR-0037 reduction leads; a faster
   default core is gated on showing these are SAT-search-bound after reduction.

The decided count now scales with both budget (3 s → 4, 20 s → 7) and reduction
depth (each `EncodingBudget` instance pulled under the ceiling is a new decision),
which is the tractable, measured growth path.

## Are the 99 Timeouts SAT-search-bound or size-bound? (2026-06-18, measured with kissat)

The `+4` win was *entirely* `EncodingBudget→decided`; the 99 Timeouts did not move
(99→99). The open crux (ADR-0037's reopening trigger): are the Timeouts *encodable
but search-hard* (a stronger SAT core would crack them) or *genuinely too large*
(only reduction helps)? Measured directly: bit-blast each Timeout's CNF to DIMACS
(`axeyum-bench/examples/dump_dimacs.rs`, same preprocessing pipeline) and run the
state-of-the-art **kissat 4.0.4** on what batsat times out on at 20 s.

| instance | CNF clauses | batsat @20s | **kissat** | xor_cdcl (in-tree) | PBLS (word-level LS) |
|---|---|---|---|---|---|
| `mobiledevice_…na6_nr3_paired` | 217 k | timeout | **SAT 2.1 s** | — | timeout (2.5k flips) |
| `string1x8.4` | 150 k | timeout | **SAT 8.3 s** | **>120 s, no result** | timeout (2.7k flips) |
| `string1x8.7` | 150 k | timeout | **SAT 14.7 s** |
| `string1x8.1` | 291 k | timeout | **SAT 18.0 s** |
| `string2x8.6` | 651 k | timeout | timeout (25 s) |
| `string4x8.2` | 1.38 M | timeout | timeout (30 s) |
| `string4x16.9` | 7.81 M | timeout | timeout (30 s) |

**The answer is BOTH, split sharply by CNF size:**

- **The small-CNF Timeouts ARE SAT-search-bound.** kissat cracks every one ≤ ~300 k
  clauses (2–18 s) that batsat cannot touch in 20 s — `mobiledevice_paired` in 2 s vs
  batsat > 20 s is a 10×+ gap. So **a competitive default SAT core (P1.3) is a real,
  data-justified lever** that converts Timeouts reduction's encoding-ceiling work
  never reaches. By CNF-size bucket the search-bound band is **~9 of 99** (≤ 300 k).
- **The large-CNF bulk (~90, ≥ ~650 k clauses) defeats even kissat** in 25–30 s.
  Those are genuinely hard/large; a faster core alone will not crack them — they need
  **CNF reduction** (word-level `ite`/AC shrinking, the active P1.2 work) to come
  within reach, exactly as the `EncodingBudget` instances did.

**So the two destination-2 levers are complementary, partitioned by CNF size:** a
competitive SAT core for the small-CNF Timeouts; word-level reduction for the
large-CNF bulk (and the `EncodingBudget` set).

**But the core bar is kissat-class, and ALL THREE of axeyum's pure-Rust engines miss
it (measured).** On `string1x8.4` (a 150 k-clause *satisfiable* instance kissat solves
in 8.3 s): the in-tree competitive CDCL core (`solve_with_xor_cdcl` — VSIDS/Luby/LBD/
1-UIP, `examples/xor_cdcl_probe.rs`) **did not finish in 120 s**; the word-level
local-search engine (PBLS, P1.7, `examples/pbls_probe.rs`) — which *should* excel on
satisfiable structural instances — also timed out, managing only **~2 700 flips in
20 s (~135 flips/s)**: pathologically slow for WalkSAT (competitive engines do
10⁵–10⁶/s). Its bottleneck is that each candidate's `score()` re-evaluates the
assertion term *from scratch* (no memoized/incremental term evaluation), so on the
deep `ite`-nests every step costs ~8 ms. So neither CDCL (batsat), XOR-CDCL, nor
local search reaches this band — converting it needs a **kissat-class** solver, which
is a major P1.3 effort (Kissat is years of tuned C), and is **out of scope as a
default** under the pure-Rust/no-C++ rule (kissat can serve only as a feature-gated
benchmark oracle, like Z3). **Two collision-free pure-Rust optimization openings this
exposes:** (a) PBLS's per-flip cost is dominated by full-term re-evaluation — a
*memoized/incremental* term evaluator (dirty-propagate only the changed variable's
cone) could raise the flip rate by orders of magnitude and is self-contained in
`pbls.rs`; (b) the CDCL gap to kissat (data structures / inprocessing / restarts) is
the long-game. **Practical consequence:** even for the search-bound Timeouts,
**word-level reduction is the more tractable near-term lever** — shrinking the CNF
brings it within reach of the weaker core we actually ship, the same mechanism that
converted the `EncodingBudget` set.
The custom-core question is genuinely reopened (ADR-0037), but the honest bar it must
clear (kissat-class) makes reduction the higher-ROI near-term work. The pulse to
track: **Timeout→decided**, primarily via reduction, with the core gap measured
against kissat as the north star.

## Bottom line

Lazy arithmetic-CEGAR bit-blasting is now wired end-to-end (opt-in dispatch
`10a412e`, read-only entry point `3b4d390`, `LazyBvBackend` `3baa0dc`, bench
backend `f6cb39c`) with `DISAGREE=0` preserved — sound and ready for the corpora
it fits. **But the public 113 measurement proves that slice is `ite`/size-bound,
not multiplier-bound: lazy is a no-op there (2/113 = eager).** The honest
destination-2 lever for *this* corpus is formula-size reduction (word-level `ite`
handling + P1.2 preprocessing + broader-than-arithmetic abstraction), not
multiplier CEGAR. Measure `--preprocess` on this slice next.
