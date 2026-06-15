# 01 — Dependency DAG, keystones, and execution order

This is the shape of the work: what unblocks what, where the keystones are, and
the order to actually do it in. The plan is four parallel tracks, but they are
not independent — the arrows below are the real constraints.

## The cross-track DAG

```
                         ┌─────────────────────── TRACK 1: ENGINE & PERFORMANCE ───────────────────────┐
                         │                                                                              │
  P4.5 benchmarking ───► P1.1 SAT inprocessing ──┐                                                      │
  (measure first)        P1.2 preprocessing ──────┼──► measured QF_BV performance ──► (Z3 perf parity)  │
                         P1.3 SAT-core modern ────┘                                                      │
                         P1.7 PBLS engine (portfolio, parallel) ──────────────────────────────────────► │
                         │                                                                              │
                         P1.4 e-graph ◄══ KEYSTONE ══► P1.5 CDCL(T) loop ──► P1.6 theory combination    │
                         └───────┬──────────────────────────┬───────────────────────┬─────────────────┘
                                 │                           │                       │
            ┌────────────────────▼───────────┐   ┌───────────▼─────────┐  ┌──────────▼───────────┐
            │ TRACK 2: THEORIES               │   │ (enables lazy        │  │ (enables multi-theory │
            │ P2.3 EUF  ─► P2.2 arrays-lazy   │   │  everything)         │  │  QF_AUFLIA etc.)      │
            │ P2.1 BV-lazy   P2.9 dt-lazy     │   └─────────────────────┘  └──────────────────────┘
            │ P2.4 LIA cuts (independent)     │
            │ P2.5 NRA/CAD (independent, XL)  │
            │ P2.6 quantifiers ◄── needs e-graph + MAM
            │ P2.7 strings   P2.8 FP polish (independent)
            └─────────────────────────────────┘

  ┌──────────────────────────── TRACK 3: PROOFS & LEAN (mostly parallel to Track 1) ───────────────────────────┐
  │ P3.0 trust ledger ─► P3.1 LRAT ─► P3.2 Alethe IR ◄══ KEYSTONE ══► P3.3 Alethe QF_BV ─► P3.4 embedded checker │
  │                                           │                                  │                              │
  │                                           └────► P3.5 reduction proofs ──────┘──► P3.6 Lean kernel ─► P3.7   │
  │                                                  (needs Track 2 reductions)        (capstone)    reconstruct │
  └────────────────────────────────────────────────────────────────────────────────────────────────────────────┘

  TRACK 4: USE CASES & FRONTEND
  P4.1 warm lazy memory ◄ needs P1.4/P1.5 (or interim eager) ─► P4.2 CFG frontend (angr/unicorn-class)
  P4.3 OMT/MILP (independent)   P4.4 SMT-LIB surface (independent)   P4.5 benchmarking (do FIRST, gates Track 1)
```

## The two keystones

1. **Incremental e-graph + CDCL(T) loop** (P1.4 → P1.5). The e-graph is the
   equality bus, the model substrate, and the proof forest; the CDCL(T) loop is
   the SAT-trail → theory-`check()` → propagate-back cycle. Together they convert
   axeyum's eager/one-shot theories into lazy, integrated ones. **Blocks:** P2.2
   (lazy arrays), P2.3 (EUF), P2.6 (quantifiers — e-matching walks the e-graph),
   P2.9 (datatypes), P1.6 (combination), and the warm side of P4.1.
2. **Alethe term/proof IR + emitter** (P3.2). The Rust-checkable (Carcara),
   BV-shaped, Lean-on-ramp proof format. **Blocks:** P3.3, P3.4, P3.5, and the
   reconstruction in P3.7.

## Critical paths

- **To Z3 performance parity:** `P4.5 → P1.1 (BVE) + P1.2 (word-level preproc) →
  measure → P1.3 → measure`. PBLS (P1.7) runs in parallel as a portfolio partner
  for satisfiable instances.
- **To Lean parity:** `P3.0 → P3.2 (Alethe IR, keystone) → P3.3 (Carcara-checked
  QF_BV) → P3.5 (reduction proofs) → P3.6 (kernel) → P3.7 (reconstruction)`.
  P3.5 depends on Track 2 reductions existing in lazy/checkable form.
- **To theory breadth/perf:** `P1.4 (e-graph) → P1.5 (CDCL(T)) → {P2.2, P2.3,
  P2.6, P2.9} → P1.6 (combination)`. P2.4 (LIA cuts), P2.5 (NRA/CAD), P2.8 (FP)
  are independent and can proceed any time.

## Recommended execution order (waterfall with parallelism)

The plan is long; this is the order that maximizes early, measurable value and
keeps the trust story honest.

**Stage 0 — instrument (days).**
- P4.5 benchmarking harness: a committed, reproducible Z3 head-to-head on a small
  QF_BV slice. *Nothing in Track 1 is "done" without this baseline.*
- P3.0 trust ledger: make every trusted reduction a named, countable entry.

**Stage 1 — performance foundation + proof on-ramp (parallel, weeks).**
- Track 1: P1.2 (word-level preprocessing + AIG 2-level rewrite) and P1.1
  (subsumption → **BVE** → vivification, glue tiers). Re-measure after each.
- Track 3: P3.1 (LRAT) then P3.2 (**Alethe IR**, the keystone) → P3.3
  (Carcara-checked QF_BV). This is independent of the perf work and advances Lean.

**Stage 2 — the engine keystone (weeks–months).**
- Track 1: P1.4 (e-graph) → P1.5 (CDCL(T) loop). Build the independent congruence
  checker alongside (cheap, on-identity).
- Track 3: P3.4 (embedded Alethe checker subset) in parallel.

**Stage 3 — theories on the keystone (months).**
- Track 2: P2.3 (EUF) → P2.2 (lazy arrays) → P2.1 (lazy BV) → P2.9 (datatypes);
  P2.4 (LIA cuts) and P2.8 (FP) anytime; P2.6 (quantifiers) after the e-graph.
- Track 1: P1.6 (theory combination) once ≥2 theories share the e-graph.
- Track 3: P3.5 (reduction proofs) retiring trust-ledger entries as each theory
  gains a checkable reduction.
- Track 4: P4.1 (warm lazy memory) once P1.4/P1.5 land; P4.3/P4.4 anytime.

**Stage 4 — the hard frontiers (multi-month each).**
- Track 2: P2.5 (NRA/CAD), P2.7 (full strings), P2.6 (MBQI/QE maturity).
- Track 3: P3.6 (Lean kernel) → P3.7 (Alethe→Lean reconstruction) — the capstone.
- Track 4: P4.2 (angr/unicorn-class CFG frontend).

## Sequencing principles

- **Measure between every performance change** (Stage 1). One variable at a time.
- **The e-graph is worth waiting for** — resist bolting lazy behavior onto the
  eager reductions; build P1.4/P1.5 and migrate cleanly.
- **The proof track does not need the perf track** — P3.0→P3.3 can run from day
  one in parallel, and each step is independently shippable and checkable.
- **Keep the trust ledger going to zero** — every reduction that becomes lazy
  (Track 2) should get its Alethe reduction proof (P3.5) and drop a ledger entry.
