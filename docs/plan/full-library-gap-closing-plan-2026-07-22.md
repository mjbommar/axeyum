# Full-Library Gap-Closing Plan — 2026-07-22

**Method: work backwards from the actual SMT-LIB library and our own measured run.**
This plan is grounded in two empirical anchors that most prior planning docs only
estimated:

1. **The whole SMT-LIB 2024 non-incremental library is now staged** on `/nas3`
   (`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/` — **438,631**
   benchmarks across 84 logics; incremental release also fetched, 44,333).
2. **A live full-library run is in flight on `s4`** — the SMT-COMP §6-selected
   subset (**64,345** files, seed `20260721`) through
   `crates/axeyum-bench/examples/smtcomp_cli.rs` at a 300 s ceiling, scored by
   `scripts/smtcomp_repro/`. It is the first time axeyum's per-logic
   decide/decline/**wrong** map is measured against the real library at scale.

**This does not replace the current authoritative queue.** The operative ranked
program remains
[`gap-analysis-z3-lean-2026-07-21.md`](gap-analysis-z3-lean-2026-07-21.md)
(gaps **G0–G10** + its 10-item next-actions list). This document adds the
*full-library empirical layer* those gaps were designed to measure (G1's
coverage-weighted matrix, G2's production depth, G3's neutral correctness) and
records **two P0 defects the run surfaced**. Read the two together; where they
conflict, the *measured* number wins (that is literally G0).

Cross-references use the existing plan spine: Track/Phase IDs from
[`docs/plan/README.md`](README.md) and the tracks, the dependency DAG in
[`01-dependency-dag.md`](01-dependency-dag.md), and the golden-tested per-fragment
status in
[`../research/08-planning/support-matrix.md`](../research/08-planning/support-matrix.md)
and [`capability-matrix.md`](../research/08-planning/capability-matrix.md).

---

## 0. P0 — Soundness defects found by the run (block every parity claim)

The stale run caught both directions of wrong verdict on real SMT-LIB
benchmarks. They invalidate the DISAGREE = 0 soundness floor until repaired, so
they are **ahead of every decide-rate item below**.

### P0-A — FP wrong-`sat`

- **File:** `QF_ABVFP/20170428-Liew-KLEE/imperial_synthetic_fadd_to_exact_zero_klee_float.x86_64/query.26.smt2`
  (declared `:status unsat`).
- **Verdict disagreement:** axeyum returns **`sat`** in 0.12 s; **cvc5 1.3.4**,
  **Bitwuzla 0.9.1**, and the declared status all say **`unsat`**. Two independent
  reference solvers + ground truth agree → genuine wrong-`sat`.
- **Isolation:** the arrays-free QF_BVFP twin (`QF_BVFP/…/query.26.smt2`) is
  **also** wrong-`sat`, so the bug is in the **pure floating-point path**, not the
  array combination. The distinctive operator is `(fp.add roundTowardNegative …)`
  — FP addition under a **non-default rounding mode**, alongside `((_ to_fp 8 24)
  bv)`, `fp.isNaN`, `fp.abs`, `fp.isInfinite`.
- **Repro preserved:** [`../../bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/`](../../bench-results/smtcomp-full-library-20260722/soundness-fp-wrong-sat/)
  (both `.smt2` files + provenance).

**Status: root cause fixed locally; full-slice revalidation remains open.** The
finite add path forced every exact nonzero cancellation to `+0`. Under
`roundTowardNegative`, IEEE/SMT-LIB semantics require `-0`; the same latent
convention existed in FMA. Because model replay evaluates the same lowered FP
circuit, it could not independently detect the bad convention. The local fix
selects the exact-zero sign from the rounding mode for both add and FMA.

**Exit criteria** (per the project Hard Rules on underspecified/edge operators):
1. **DONE:** root-cause and repair exact-cancellation/signed-zero selection in
   `axeyum-fp::add` and `axeyum-fp::fma`.
2. **DONE:** add bit-for-bit `rustc_apfloat` tests over all five rounding modes,
   a minimized QF_FP regression, and a differential fuzz seed-class. The random
   generator now draws every rounded FP operator from all five modes and has a
   deterministic coverage assertion. A 600-script cvc5 1.3.4 run jointly
   decided all 600 (267 `sat`, 333 `unsat`) with **0 disagreements**; 15 directed
   add/FMA cancellation cases also agree.
3. **PARTIAL:** the preserved full QF_BVFP and QF_ABVFP twins now both return
   `unsat` through the SMT-COMP CLI. Re-run the complete QF_FP/QF_BVFP/QF_ABVFP
   selected slices before declaring the new full-library soundness floor
   restored to DISAGREE = 0.
4. This maps onto Track 3 **P3.0** (trust ledger) and the **P2.8** FP row
   ([`track-2-theories/README.md`](track-2-theories/README.md)); the fuzz-coverage
   rule is the FP analogue of the div/mod-by-0 lesson (ADR referenced in CLAUDE.md).

### P0-B — QF_AUFLIA wrong-`unsat`

- **File:** `QF_AUFLIA/array_benchmarks/misc/pipeline-invalid.smt2`, declared
  `:status sat`; exact SHA-256
  `dc7f8f51be688669321c8a9a15f2543fc070bc3a4c55b81c763604c34fa73bde`.
- **Verdict disagreement:** the staged stale binary returned `unsat` in 12.10 s.
  Current Axeyum reproduced `unsat`; cvc5 1.3.4 returned `sat` immediately.
  cvc5 also returned `sat` after Axeyum parsed and sharing-preservingly rewrote
  the script, ruling out a stale-binary or parser/round-trip explanation.
- **Boundary:** the lazy-ROW adapter reduces arrays to a scalar QF_UFLIA
  abstraction. Both Axeyum scalar searches refute this satisfiable abstraction,
  but neither produces an independently checked proof that can be lifted through
  the array abstraction. Exporting that search result contradicted the existing
  foundational DAG contract: integer-bearing `unsat` without evidence must
  decline.
- **Repair:** the QF_AUFLIA lazy-ROW adapter now converts such unchecked scalar
  refutations to `unknown`. Cheap certificate-rechecked array refuters still run
  before the adapter, so proven array UNSAT coverage is retained. The exact
  public benchmark is committed under the curated QF_AUFLIA corpus and pinned by
  a no-wrong-verdict regression.

**Exit criteria:** the exact regression never returns `unsat`; a future regain
of this UNSAT coverage requires a small independently checked scalar proof plus
an explicit lift through the array abstraction, not agreement between two
untrusted search paths.

> **Why the monitor missed it:** the alerts-only s4 monitor had lapsed between
> re-arms; the wrong answer was caught by this analysis pass reading the shard
> logs. Action item G-ops: keep a persistent WRONG grep over the shard logs for
> the remainder of the run (cheap, and soundness is the crown jewel).

---

## 1. The library, by the numbers (what "the gap" actually weighs)

Working backwards means weighting each fragment by **how many real benchmarks it
represents**, not by how interesting the theory is. Top logics by count in the
staged non-incremental library:

| Logic (dir) | benchmarks | §6-selected | family |
|---|---:|---:|---|
| QF_SLIA | 84,395 | 8,839 | strings + int |
| QF_BV | 46,191 | 5,019 | bit-vectors |
| QF_FP | 40,407 | 4,440 | floating-point |
| QF_NIA | 25,443 | 2,944 | nonlinear int |
| AUFLIRA | 20,011 | 2,401 | **quantified** array+UF+arith |
| QF_S | 18,940 | 2,294 | strings |
| QF_ABVFP | 18,129 | 2,212 | array+BV+FP |
| QF_BVFP | 17,249 | 2,124 | BV+FP |
| QF_ABV | 15,148 | 1,914 | arrays |
| UFNIA | 13,464 | 1,746 | **quantified** UF+nonlinear int |
| QF_LIA | 13,306 | 1,730 | linear int |
| QF_NRA | 12,154 | 1,615 | nonlinear real |
| AUFDTLIRA | 11,043 | 1,504 | **quantified** array+UF+DT+arith |
| UFLIA | 10,128 | 1,412 | **quantified** UF+linear int |
| QF_DT | 8,700 | 1,270 | datatypes |
| (… 69 more logics) | | | |

Two structural facts jump out:
- **Strings dominate by volume**: QF_SLIA + QF_S ≈ **103k benchmarks (24 % of the
  library)**.
- **Quantified logics are a huge block**: AUFLIRA + UFNIA + AUFDTLIRA + UFLIA +
  the quantified `BV`/`LIA`/`LRA`/`NRA`/`ALIA`/`ANIA`/… together are **> 100k
  benchmarks**, and they sort *first* alphabetically (which is why the live
  overall decide-rate reads low early — see §2).

---

## 2. Measured gap: axeyum (s4) vs the state of the art (SMT-COMP 2024)

Three different measurements, kept explicitly separate (do not conflate — G0):

- **axeyum @ s4** — the live full-library §6 run, 300 s ceiling, shared hardware.
  Partial (~32 % through at the latest audit) and running a stale binary. It is
  diagnostic-only because it predates both P0 repairs and the E1b-E3 durability
  protocol.
- **axeyum @ SCOREBOARD** — the committed curated-regression decide-rate vs
  z3 4.13.3 ([`../../bench-results/SCOREBOARD.md`](../../bench-results/SCOREBOARD.md)):
  **753/992 ≈ 76 %, DISAGREE = 0** over 680 oracle-compared.
- **top solver @ SMT-COMP 2024** — best solver on the selected+scrambled division,
  1200 s ([results](https://smt-comp.github.io/2024/results/)).

| Fragment | library ct | axeyum s4 decide% | axeyum SCOREBOARD | top solver @ SMT-COMP'24 | gap character |
|---|---:|---:|---|---|---|
| **QF_ABVFP** | 18,129 | **90 %** | — | (in QF_FP family) | strong — **but P0 wrong-sat here** |
| **QF_ABV** | 15,148 | **91 %** | 88 % (169/193) | Bitwuzla **99.7 %** (7,553/7,574) | close; hard-tail + budget |
| **QF_AUFLIA** | small | 73 % | 71 % (5/7) | — | mid; **P0 wrong-unsat in stale run** |
| **QF_AUFBV** | small | 49 % | 56–93 % | — | mid |
| **strings** QF_SLIA | 84,395 | *(not yet reached)* | **36 %** (18/50) — weak | cvc5-class ~65–80 % | **biggest volume gap** |
| **strings** QF_S | 18,940 | *(not yet)* | 65 % (87/134) | — | volume + sat-direction |
| **QF_BV** | 46,191 | *(not yet)* | 100 % on curated `bvred`; **~7 %** on hard p4dfa | Bitwuzla **98 %** (10,489/10,703) | **perf** on hard tails |
| **QF_FP** | 40,407 | *(not yet)* | 100 % (16/16 curated) | Bitwuzla **91.6 %** (252/275) | strong; P0 fix first |
| **QF_LIA** | 13,306 | 45 % (partial) | 91 % (10/11) | OpenSMT **93.6 %** (4,514/4,825) | close on QF; budget |
| **QF_NIA** | 25,443 | *(not yet)* | 85 % (33/39) | — | frontier (P2.5) |
| **QF_NRA** | 12,154 | *(not yet)* | 84 % (32/38) | — | **the measured frontier** (P2.5) |
| **UFLIA** (quant) | 10,128 | ~1 % | 0/5 (weak) | **cvc5 57 %** (1,628/2,849) | **biggest capability gap** |
| **AUFLIRA** (quant) | 20,011 | **0 %** | not measured | — | quantifier support absent |
| **AUFDTLIRA** (quant) | 11,043 | **0 %** | not measured | — | quantifier + DT |
| **UFNIA** (quant) | 13,464 | *(partial)* | not measured | — | quantifier + nonlinear |

**The headline read:** on axeyum's *supported QF fragments* it is
competitive-but-behind (arrays 88–91 %, FP/BV strong on curated, LIA/LRA ~90 %) —
the gap there is **budget + hard-tail performance**. The overall number is dragged
down by two structural gaps: **strings** (huge volume, weak decide) and
**quantified logics** (huge volume, ~0 % decide). Critically, on the quantified
block **the champions still decide a lot** (cvc5 gets 57 % of UFLIA where axeyum
gets ~1 %) — so it is a *real capability gap*, not "everyone declines these."

Note also, from SMT-COMP, that **even the best solver tops out at ~57 % on
quantified UFLIA** — quantifiers are hard for everyone. Parity there means *honest
`unknown` + a competitive decided fraction*, not 100 %.

---

## 3. Rank-ordered gap-closing program

Ranked by **(benchmark volume × decide-gap × tractability)**, reconciled with the
existing priority orders in
[`gap-analysis-z3-lean-2026-07-21.md`](gap-analysis-z3-lean-2026-07-21.md) (G0–G10),
[`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) (leverage
order), and [`decide-rate-frontier-2026-06-28.md`](decide-rate-frontier-2026-06-28.md).

### Rank 0 — Fix both P0 wrong verdicts (soundness floor)
See §0. FP code repair and focused validation are complete, with full affected
slices open. AUFLIA now sound-declines the unchecked scalar refutation and pins
the exact benchmark. Nothing ships as "parity" until fresh affected slices use
the repaired binary and return DISAGREE = 0. Track 3 **P3.0** / **P2.8** plus
the foundational array/UFLIA evidence boundary.

### Rank 1 — Finish the measurement itself (G0–G3), because it re-ranks everything
The s4 run *is* the instrument the current queue asked for. Complete it, then
regenerate G1's coverage-weighted parity matrix from the actual per-logic results.
- **G0** stop docs overruling measurements; **G1** coverage-weighted matrix;
  **G2** production depth; **G3** neutral correctness (add cvc5/Bitwuzla as
  co-oracles on the same 64,345 files — we already run them as reference).
- Existing infra to reuse: `scripts/smtcomp_repro/`, plus the resumable-run design
  in [`smtcomp-resumable-run-design-2026-07-21.md`](smtcomp-resumable-run-design-2026-07-21.md)
  and [`smtcomp-full-library-candidate-run-handoff-2026-07-21.md`](smtcomp-full-library-candidate-run-handoff-2026-07-21.md)
  (ADR-0343/0344 — do **not** merge the two scores; keep the selector-eligibility
  exclusions).
- **Exit:** a committed per-logic decide/decline/wrong table over the full §6
  selection, cvc5/Bitwuzla-cross-checked, feeding a fresh `SCOREBOARD.md` sibling.

### Rank 2 — Strings (the volume king): P2.7 unbounded/length-aware
QF_SLIA (84k) + QF_S (19k) ≈ **103k benchmarks, ~24 % of the library**, and
axeyum is weak here (36 % QF_SLIA committed). Largest single decide-rate lever by
volume. The cheap-encoding-first advice (decide-rate-frontier §2) applies before
proof investment.
- Lives in **P2.7** ([`track-2-theories/P2.7-strings.md`](track-2-theories/P2.7-strings.md),
  sub-program `track-2-theories/P2.7-strings/`). Phase A done; residual = unbounded
  `str.len` unsat, concat-emptiness, extended `str.*`/sequence coupling, Nielsen
  transform (ADR-0025/0029/0052/0053/0054/0061).
- Prereqs: BV+LIA combination (**P1.6**, landed conjunctive) and the sat-direction
  machinery shared with quantifiers.
- **Exit:** QF_SLIA/QF_S decide-rate on the s4 selection ≥ (measured cvc5 baseline
  − 10 pts), DISAGREE = 0.

### Rank 3 — Quantifier sat-direction (MBQI model-finding, T2.6.5): P2.6
The **biggest capability gap** — >100k quantified benchmarks at ~0 % decide, where
cvc5/Z3 decide a real fraction. This is called out as *the* categorical hole in
[`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) (leverage
2a) and the Track-1 keystone in
[`decide-rate-frontier-2026-06-28.md`](decide-rate-frontier-2026-06-28.md) (item 3).
- Lives in **P2.6** ([`track-2-theories/P2.6-quantifiers.md`](track-2-theories/P2.6-quantifiers.md)).
  Finite expansion + E-matching + narrow MBQI **landed** (ADR-0016/0095–0141, ~35
  `quant_*.rs` modules); the hole is the **general sat-direction**:
  - **T2.6.5** general model-based instantiation (`mbqi_model_finder.rs` is narrow),
  - **T2.6.1** the MAM (bytecode E-matching abstract machine, generation-cost
    scheduling — explicitly open in the support-matrix),
  - **T2.6.2** general trigger inference / multi-triggers.
- **Gated on the e-graph + CDCL(T) keystones** — *"e-matching walks the e-graph"*
  ([`01-dependency-dag.md`](01-dependency-dag.md): the e-graph blocks P2.2, P2.3,
  **P2.6**, P2.9, P1.6). Keep the soundness stance: broaden the *search* (untrusted
  instantiation), keep the *check* (models replay; unsat carries checked instances).
- **Exit:** quantified UFLIA/AUFLIA/AUFLIRA decide-rate off the floor
  (target: a measured fraction approaching cvc5's on the same selection), 0 wrong.

### Rank 4 — Complete the CDCL(T) keystone migration (P1.4 → P1.5)
Not a decide-rate line itself, but the **enabler under Ranks 2–3 and arrays**. Both
keystones are *partially built* — a live backtrackable e-graph (ADR-0077) and a
`CdclT<T>` driver with 1-UIP + EUF/String adapters exist; the remaining work is
**porting arrays/BV/datatypes onto the spine + the default-dispatch ADR**
([`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) Gap 3),
not building the driver. Do this in parallel with the measurement lane.
- **P1.4/P1.5** ([`track-1-engine/README.md`](track-1-engine/README.md)); unblocks
  **P2.2** lazy arrays, **P2.3** EUF-on-loop, **P2.6** quantifiers, **P1.6**
  combination.

### Rank 5 — Nonlinear arithmetic (the measured frontier): P2.5, NIA before NRA
QF_NIA (25k) + QF_NRA (12k). [`measured-scoreboard-2026-07-01.md`](measured-scoreboard-2026-07-01.md)
calls NRA/NIA *"the frontier … by a wide margin."* Honest `unknown` is acceptable
parity on the undecidable tail, so this ranks **below** volume/quantifier levers.
- **P2.5** ([`track-2-theories/P2.5-nra-cad.md`](track-2-theories/P2.5-nra-cad.md),
  sub-program `P2.5-nra/`, funded ADR-0058). CAD decision side complete;
  open arc = per-cell Positivstellensatz proof reconstruction (ADR-0044/0045/0046)
  and the NIA residue path (ADR-0024). Independent of the keystones.

### Rank 6 — QF_BV / QF_FP hard-tail performance: Track 1 measurement (P4.5 → P1.1/P1.2)
On the QF fragments axeyum decides, the gap to Bitwuzla is **speed** (it rides the
300 s ceiling on hard multipliers / p4dfa). The inprocessing (P1.1 BVE) and
word-level preprocessing (P1.2) passes are **built but default-off**
([`gap-analysis-z3-cvc5-2026-07-07.md`](gap-analysis-z3-cvc5-2026-07-07.md) leverage
1). The next step is *measure-and-flip*, gated by **P4.5** (the PAR-2 head-to-head,
landed). Low build cost, pure measurement + flag flips.

### Rank 7 — Proof/Lean coverage as a first-class denominator: G5/G6, Track 3
Parity's *other* axis. Make proof coverage a measured denominator (G5) and external
Lean checking a required tiered gate (G6). Extend Alethe/Lean reconstruction beyond
the admitted classes (P3.5/P3.7); the Lean-system compatibility work (TL2.x / G7)
proceeds independently. This is the differentiator, not raw coverage — prioritize
it *alongside* Rank 1's measurement so every new decided-unsat carries evidence.

### Rank 8 — Breadth backlog (P2.10), demand-pull only
Sets/bags, separation logic, co-datatypes, rec-fun, sequences — the columns Z3/cvc5
have and we don't. **Counted, not built** (STATUS.md). Do not chase; the north star
explicitly gates on measured parity, not theory breadth.

---

## 4. How this feeds the existing plan (the measurement lane)

The s4 run is the concrete instrument the current queue
([`gap-analysis-z3-lean-2026-07-21.md`](gap-analysis-z3-lean-2026-07-21.md))
specified but had not yet executed at full scale:

- **→ G1 (coverage-weighted parity matrix):** the per-logic decide table replaces
  the single aggregate decide-rate with a benchmark-weighted matrix.
- **→ G2 (production depth):** measured on real KLEE/industrial families (e.g. the
  Liew-KLEE QF_ABVFP set that surfaced the P0), not isolated wins.
- **→ G3 (neutral correctness):** cvc5 + Bitwuzla are already run as references on
  the same files — promote them to committed co-oracles.
- **→ G5/G6 (proof denominator, Lean gate):** every decided-unsat in the run is a
  candidate for the evidence pipeline.
- **Reuse, don't rebuild:** the resumable-run design + selector-eligibility
  contracts already exist
  ([`smtcomp-resumable-run-design-2026-07-21.md`](smtcomp-resumable-run-design-2026-07-21.md),
  [`smtcomp-full-library-candidate-run-handoff-2026-07-21.md`](smtcomp-full-library-candidate-run-handoff-2026-07-21.md),
  ADR-0343/0344). Fold `scripts/smtcomp_repro/` into that contract rather than
  forking it.

---

## 5. Concrete next actions (rank-ordered, checkable)

1. **[P0 validation]** Re-run the full QF_FP/QF_BVFP/QF_ABVFP selected slices
   with the exact-zero repair and the QF_AUFLIA slice with the unchecked-UNSAT
   gate → DISAGREE 0. Focused FP tests/fuzz and the exact AUFLIA regression are
   already green.
2. **[measurement durability]** E1b is fixture-complete. Implement E2 real
   one-host aggregate enforcement and E3 multi-host loss/retry, then close the
   independent official eligibility/status/difficulty selection ledger. The
   currently running stale s4 job may inform diagnostics but receives no
   measurement credit and must not be promoted merely because it finishes.
3. **[measurement]** Only after (2), stage the repaired binary and execute the
   selected population into a versioned resumable run; `inventory.py` then emits
   the dated per-logic decide/decline/wrong record and charts.
4. **[G3]** Score the same 64,345 files with cvc5 + Bitwuzla (already staged) →
   committed three-solver per-logic comparison; this *is* the "full universe"
   reference the earlier question asked for.
5. **[G1]** Regenerate the coverage-weighted parity matrix from (3)+(4); reconcile
   with `SCOREBOARD.md` (different corpora — keep both, label clearly).
6. **[Rank 4]** Land the CDCL(T) default-dispatch ADR + begin porting arrays onto
   the spine (unblocks Ranks 2–3).
7. **[Rank 3]** Scope **T2.6.5** (general MBQI model-finding) + **T2.6.1** (MAM)
   against the *measured* quantified-logic residual shapes from (2), not from
   estimates — pick mechanisms from real decline data (G4 discipline).
8. **[Rank 2]** Scope the string decide-rate lever (cheap encoding first) against
   the measured QF_SLIA/QF_S residuals once the run reaches them.
9. **[Rank 6]** Flip + measure P1.1/P1.2 inprocessing on the QF_BV hard-tail
   families; PAR-2 delta vs Bitwuzla on the s4 QF_BV slice.

---

## Provenance

- Library: SMT-LIB 2024 non-incremental (Zenodo 11061097) + incremental (11186591),
  staged `/nas3/data/axeyum/corpus/smtlib-2024/`.
- Run: `scripts/smtcomp_repro/` (harness commit `f80b697b`+),
  `crates/axeyum-bench/examples/smtcomp_cli.rs`, §6 selection seed `20260721`,
  300 s ceiling, host `s4`.
- References: cvc5 1.3.4, Bitwuzla 0.9.1 (`references/smtcomp-solvers/`);
  SMT-COMP 2024 Single Query results (linked inline).
- Roadmap sources cross-referenced: `docs/plan/` (tracks, DAG, gap-analyses),
  `docs/research/08-planning/{support-matrix,capability-matrix,foundational-dag,roadmap}.md`,
  `bench-results/{SCOREBOARD,DOMINANCE}.md`.
