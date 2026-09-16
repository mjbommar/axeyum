# Lane: `lra-model-replay` — what arithmetic is actually outside the incremental LRA engine

<!-- plan-section: lane-status -->

**Lane LRA-MODEL-REPLAY (`CENSUS COMPLETE, PREMISE REFUTED, NO CODE SHIPPED`,
lra-model-replay, 2026-09-16.)**
Reads: [ADR-2111](../../research/09-decisions/adr-2111-qf-lra-what-the-same-simplex-does-differently.md)
(§6 item 2, "model did not replay"),
[ADR-2045](../../research/09-decisions/adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md),
[ADR-2055](../../research/09-decisions/adr-2055-the-tableau-is-the-memory-and-capping-it-costs-eighteen-clean-exits.md),
[ADR-2125](../../research/09-decisions/adr-2125-a-warm-simplex-basis-across-sat-decisions.md),
[ADR-2132](../../research/09-decisions/adr-2132-a-builds-per-file-screen-for-the-warm-basis.md),
and `bench-results/lra-atom-screen-20260916/README.md`.
Artifacts: `bench-results/lra-model-replay-20260916/`.
Compute: s7, physical core pairs `1,9` (baseline) and `3,11` (census), run
concurrently on disjoint pairs; 24 s / 8 GiB; `$EPOCHREALTIME` with a unit
self-check before any solve (205 ms read for a 200 ms sleep on both arms).

### The finding

The string this whole line of work is blocked on —

> `online CDCL(T) LRA model did not replay (arithmetic outside the
> incremental engine)` (`lra_theory.rs:491`, `:502`)

— **is wrong about its own subject on most of the files it is printed for.**
Across the entire measured target population the count of atoms the
incremental engine could not represent (`AtomKind::Unsupported`) is **zero**.
Every atom linearizes. There is no arithmetic outside the engine.

**The histogram**, over the 47 pinned `QF_LRA` files where the replay wall is
the FINAL answer at `AXEYUM_LRA_ATOM_SCREEN=16` (53 files hit the wall; 6 are
rescued by a later route; the 47 are exactly the 53 ∩ LRA-TRACE's 93
undecided, and the 6 are exactly the 6 outside it):

| bucket | files | tableau | clock |
|---|---:|---|---|
| no model — Fourier–Motzkin witness extraction declined | **27** | ABSENT | still available |
| **disequality** — equality asserted FALSE; model built, replay failed | **11** | present | n/a |
| no model — simplex re-check refused at pivot 0 | **7** | present | **gone** |
| no model — Fourier–Motzkin declined | **2** | ABSENT | gone |

Atoms the engine could not represent, summed over all 47 files: **0**.

Three different failures hide behind the one sentence, and only one of them
is a construct:

1. **The tableau never existed.** The warm simplex is `None`, so
   `LraTheory::model` (`lra_online.rs:2439`) extracts the witness by a full
   Fourier–Motzkin elimination of every variable (`solve_values`,
   `lra_online.rs:3783-3808`), which declines on its own budget **with the
   deadline still available**. The tableau is absent because the online route
   admits on `TableauAdmission::DenseCells` (`lra_online.rs:1308`) —
   `m × (nvars+m) > MAX_TABLEAU_CELLS` at `simplex.rs:2090` — a **dense-cell
   count over storage ADR-2111 made sparse**. The nonzero currency exists in
   the same file (`lra_online.rs:2144`, `simplex.rs:2047-2063`) and the
   online route does not use it; its own doc says so at `:1312-1314`.
2. **The clock was gone.** `model` re-runs `Incremental::check` before
   materializing (`lra_online.rs:2443`), and `Tableau::run` polls the
   deadline at pivot 0 (`simplex.rs:1441`), so an expired budget returns
   `Unknown` before a single pivot — while `Incremental::point`
   (`simplex.rs:2287`) takes `&self` and does no solving. These are timeouts
   wearing an incompleteness label. Where the budget went is in the same
   trace: `theory_propagate_ms=18781` of 24,000 on one file, buying 249
   propagations against 1,186,982 decisions (`LraTheory::propagate`,
   `lra_online.rs:2501`, rescans every atom per call and runs up to two full
   simplex probes per unassigned order atom) — ADR-2111 §6's "propagation is
   absent", now shown to *cause* the reported non-replay.
3. **The disequality — the only real construct.** The model was built, the
   failing assertions evaluate `false` (not to an evaluation error), and the
   only offending atoms inside them are real equalities the SAT solver
   asserted **false**. `TheorySolver::assert` drops exactly that case
   (`lra_online.rs:2610`), and the comment above it (`:2588-2593`) claims the
   case cannot arise because "the driver only ever sets equality atoms true".
   That is true of the **offline** driver it names and false of the CDCL(T)
   driver this route uses: `is_lra_atom` (`lra_online.rs:5580`) admits any
   real `Op::Eq`, so the encoder gives every real equality a skeleton
   variable. The census counts them directly: on `sc-25.base.cvc.smt2`, 371
   of 776 equality atoms are asserted false, and ONE assertion out of 101
   fails to replay because of them. The bucket is the `sc-7 … sc-25`
   parametric family plus `sal/pursuit/pursuit-safety-16`; the
   `clocksynchro_{2,4,6,8}clocks` family and `sc-5` hit the identical wall and
   are rescued by a later route, so the shape reaches 16 files and costs the
   verdict on 11.

`distinct`, `to_real`, `to_int` and `is_int` appear in **zero** of the pinned
200 files textually, so they were never candidates. `ite` (49 files) and `/`
(64 files) are present and still produce zero unsupported atoms — the
rewriter removes them upstream.

### The reference side, for whoever picks this up

Both cited lines were re-read and verified verbatim, not inherited.

* **z3 is eager**: `new_diseq_eh` (`theory_lra.cpp:1076-1080`) hands every
  disequality to `arith_eq_adapter`, which emits three "triangle-eq" theory
  axioms (`arith_eq_adapter.cpp:208-210`, the third being
  `(x=y) ∨ ¬(x≤y) ∨ ¬(x≥y)`) so the SAT solver does the case split. The LP
  never sees a disequality. The old `theory_arith` removed disequality
  handling in Z3 2.0 for the same reason (`theory_arith_core.h:3146-3148`).
* **cvc5 is lazy and model-driven, and is the near shape**: queue it
  (`theory_arith_private.cpp:1046-1050`), and at full effort compare the
  `DeltaRational` assignment against the RHS, emitting
  `(or (<= x y) (>= x y))` only when they are equal (`splitDisequalities`
  `:4251`, test `:4271-4286`, lemma `constraint.cpp:1281-1286`, invoked from
  `postCheck` `:4006-4009`).

We already **detect** the violation — that is exactly what the `replays` gate
at `lra_theory.rs:498` does. We turn it into `unknown` instead of into a
lemma and a continued search. The missing piece is the loop-back, not a
decision procedure.

### Baseline, re-derived not inherited

Pinned 200 re-extracted from `bench-results/board-ab-20260915/QF_LRA.tsv`
(200 rows, 200 distinct paths), byte-identical to LRA-ATOM-SCREEN's list, all
200 readable on the NAS corpus. Shipped binary at `4f81de9c1`, sha256
`1ca58672…`, screen unset, s7 core pair `1,9`: **107 / 200 decided**
(66 `sat`, 41 `unsat`, 93 `unknown`, 200 exit 0) — reproducing the board's
107 exactly.

### What did NOT run

Scope was cut to the census mid-round. Reported as *did not run*, never as a
negative result: no Rust shipped, no `config_registry` entry, no lever, no
A/B, no held-out draw, no mover recheck, no differential fuzzes, no ADR
(2139 unallocated by this lane). `census-patch4.py` — the measurement that
would decide whether bucket 2's witness is already sitting in the tableau —
is written against verified anchors but **was not built or run**, so that
remains a hypothesis and must not be quoted as measured.

### Next, sized

1. **Cheapest and already half-built**: run `census-patch4.py` on bucket 2's
   files. If `sync` moved nothing and the materialized point satisfies the
   live system, reading the witness out without the re-check is a small sound
   change behind a lever, and the `replays` gate stays the guard.
2. **Bucket 1 is a currency mismatch, not a capability gap**: the online
   route can ask `TableauAdmission::Nonzeros` at `lra_online.rs:1308` the way
   the cube decider already does at `:2144`. ADR-2125 measured the two
   currencies three orders of magnitude apart.
3. **Bucket 3 needs cvc5's loop-back**: on a replay failure whose offending
   atoms are equalities asserted false, emit `(or (<= x y) (>= x y))` as a
   lemma and continue, instead of returning `unknown`. Soundness is unchanged
   — the lemma is a tautology and `replays` still gates every `sat`.
