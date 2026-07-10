# axeyum current-state audit (2026-06-15)

The baseline this plan starts from. Source of truth: `PLAN.md` history,
`crates/axeyum-solver/src/capabilities.rs` (golden-tested ledger), committed
`bench-results/`. 30 ADRs accepted; pure-Rust default, Z3 a feature-gated oracle.

## Crate inventory
| Crate | Purpose | ~lines (src) | Maturity |
|---|---|---|---|
| `axeyum-ir` | Sorts, terms, arena/interning, ground evaluator, LSB-first + `WideUint` + `Rational` | 5,105 | Mature, foundational |
| `axeyum-aig` | AIG graph: structural hashing, eval, ASCII AIGER export | 792 | Mature |
| `axeyum-bv` | Term→AIG lowering (full scalar QF_BV) + persistent `IncrementalLowering` | 2,433 | Mature |
| `axeyum-cnf` | Tseitin, DIMACS I/O, BatSat, replay maps, `IncrementalCnf`, in-tree DRAT checker, proof-producing CDCL | 4,300 | Mature; custom CDCL young |
| `axeyum-fp` | IEEE-754 builders, F16–F128 + ML formats | 6,095 | Broad; validated not certified |
| `axeyum-query` | Query object, cache keys, slicing, replay | 1,298 | Mature |
| `axeyum-rewrite` | Manifest, canonicalizer, `eliminate_arrays` | 4,811 | Solid; canonicalizer modest |
| `axeyum-scenarios` | Self-checking oracle-free workloads | 2,046 | Test/eval asset |
| `axeyum-solver` | Backend trait, all decision procedures, façade, incremental engine, BMC/symexec, DRAT exporters, Z3 backend | 15,671 | Broadest; mixed by module |
| `axeyum-smtlib` | SMT-LIB 2 reader/writer, ingestion, export | 2,914 | Solid for supported subset |
| `axeyum-bench` | Corpus harness, PAR-2, JSON artifacts | 2,337 | Mature tooling |

Total src ≈ 48k (≈63k with tests); 57 test files. Largest solver modules:
`auto.rs` 1434, `strings.rs` 1255, `lra.rs` 1489, `bitblast_miter.rs` 932,
`bmc.rs` 899, `datatype_native.rs` 745, `dpll_t.rs` 695, `nra.rs` 656,
`dpll_lia.rs` 625, `evidence.rs` 606, `incremental.rs` 557, `symexec.rs` 525.

## Capability & assurance matrix (condensed)
| Theory / feature | Assurance | Backed by |
|---|---|---|
| QF_BV (full scalar, ≤2¹⁶) | validated | replay + differential vs Z3 |
| QF_BV UNSAT (DRAT) | **checked** | `check_drat`; `UnsatProof::recheck` |
| QF_BV end-to-end (miter) | **checked** | exhaustive bit-blast faithfulness miter + DRAT, modulo independent reference |
| QF_ABV / QF_UF / QF_AUFBV | validated | eager elim/Ackermann→BV; replay; UNSAT DRAT **modulo trusted reduction** |
| QF_LRA (exact-rational) | **checked** | Farkas + exact model |
| QF_LIA / QF_LIRA | validated | replay; bounded UNSAT DRAT at chosen width |
| QF_NRA/NIA | sound-incomplete | replay (SAT), relaxation-unsat, else `unknown` |
| QF_FP (F16–F128) | validated | circuit differential vs native + `rustc_apfloat` |
| Datatypes | validated | replay; folded UNSAT DRAT-exportable |
| Quantifiers | sound-incomplete | complete on finite domains only |
| QF_S strings (bounded) | **experimental** | ADR-0052 linear `str.len` marker decides; broader coupled word/length shapes can be `unknown` |
| Optimization (MaxSAT/OMT/MILP) | **experimental** | optimum certified per-step |
| Incremental / symexec / BMC | validated | replay; SAT conflict-core; bounded-only |
| Certified k-induction | **checked** | DRAT per obligation, modulo trusted term→CNF |

**Honest read:** only QF_LRA (Farkas) and the QF_BV clausal+miter path carry
per-query independent certificates. Everything reached through a non-bit-blast
reduction is "checked **modulo trusted reduction**." FP/strings `unsat` is
replay-blind (evaluator runs the same lowered circuit), so it rests entirely on
differential validation.

## Eager vs lazy/incremental
**Eager / one-shot (dominant):** arrays (`abv.rs`, read-over-write+Ackermann
re-run per check; `check_with_memory` re-eliminates every call), UF (Ackermann),
LIA/LIRA (bit-blast to fixed width), datatypes, FP, strings, and the whole
`check_with_all_theories` pipeline.
**Genuinely incremental:** `IncrementalBvSolver` (`incremental.rs`) — warm AIG +
warm CNF over a persistent SAT solver, push/pop via selectors, learned clauses
retained; BMC/symexec ride it.
**Genuinely lazy (DPLL(T)-style):** `dpll_t.rs`/`dpll_lia.rs` over the exact
simplices, with theory propagation/conflict learning — but coupling is **purely
propositional**; there is **no Nelson–Oppen / interface-equality propagation**.
`lazy_bv.rs` is abstraction-refinement dropping heavy mul/div gadgets. The warm
path **refuses arrays** (incremental QF_ABV re-eliminates eagerly per depth).

## Performance posture (real numbers)
Two committed public QF_BV slices (SMT-LIB 2024):
1. `20221214-p4dfa-XiaoqiChen` (113 files, hard family) — Z3 4.13.3 @1s: 3 sat, 0
   unsat, **110 unknown**, PAR-2 1.96s (brutal even for Z3). sat-bv best (10s, j8,
   cnf8.5k/30k budgets): **2 sat, 0 unsat, 111 unknown**, PAR-2 19.7s, 0 oracle
   disagreements / replay failures. The one shared decision: sat-bv **3,301 ms**
   vs Z3 **1,097 ms** (~3× slower, after heavy slicing).
2. `20190311-bv-term-small-rw-Noetzli` (1575 files, easy) — sat-bv self-run @2s,
   **oracle disabled**: 87 sat + 1,329 unsat = **1,416/1575 (~90%) decided**, 159
   unknown, PAR-2 0.418s. Not cross-checked against Z3 on this slice.

**Honest summary:** no measured performance parity; no clean head-to-head where
axeyum decides a large slice at competitive PAR-2; everything gated by CNF/node
budgets. A1 (performance) is correctly the binding gate. (MEMORY warns against
sweeping the 41GB corpus — these committed runs are the deliberate baselines.)

## Proof / checking status
**Independently checkable today:** `UnsatProof::recheck` (RUP+RAT, QF_BV clausal);
`FarkasCertificate::verify` (QF_LRA); `EndToEndUnsatOutcome::recheck` (bit-blast
faithful vs independent reference + CNF DRAT — the strongest); `certify_qf_bv_by_
enumeration` (small, trusts only the evaluator); model replay (all sat); DRAT
exporters for QF_BV/ABV/UF/AUFBV/bounded-LIA/datatypes; certified k-induction.
**Still "modulo trusted reduction":** Ackermann (UF), read-over-write (arrays),
datatype/int elimination, FP lowering. No unified proof format, no independent
kernel, no Lean export.

## ADR list (one-liners)
0001 vertical slice · 0002 ground-up identity (Z3 bootstrap) · 0003 M0 IR · 0004
defer 2nd native backend · 0005 Phase-3 contracts · 0006 bit-order/lowering · 0007
first SAT adapter (rustsat-batsat) · 0008 consumer scenarios · 0009 incremental
SAT · 0010 arrays via eager elimination · 0011 DRAT + in-tree checker · 0012
proof-producing SAT core · 0013 UF via Ackermann · 0014 bit-blasted LIA · 0015 LRA
exact simplex · 0016 quantifiers (finite-domain) · 0017 WASM · 0018 SMT-LIB front
door · 0019 swappable strategies · 0020 unbounded LIA B&B · 0021 Boolean LIA via
lazy-SMT · 0022 datatype sort · 0023 FP as BV · 0024 NRA via linear abstraction ·
0025 bounded strings · 0026 float sort · 0027 MILP B&B · 0028 FP oracle
(`rustc_apfloat`) · 0029 SMT-LIB strings (equality slice) · 0030 incremental lazy
arrays (eager slice; warm lazy deferred).

## Honest gap summary — top 10 toward Z3 + Lean parity
1. **Performance parity (binding gate). Multi-month.** No measured parity; ~3×
   slower on the one shared hard instance; budget-gated. Needs preprocessing +
   SAT inprocessing + a clean Z3 head-to-head.
2. **Reduction certificates (highest Lean lever). Multi-month.** Only bit-blast is
   certified; arrays/UF/datatype/int/FP remain trusted.
3. **Warm lazy arrays. Weeks–month.** Incremental engine refuses arrays; memory
   re-eliminates eagerly. Blocks fast symexec/BMC over memory.
4. **Theory-combination / CDCL(T) Nelson–Oppen. Multi-month.** Composition is
   reduction-stacked + eager; no interface-equality propagation (the BV+LIA
   `str.len` gap stays open until this lands).
5. **Lean export + unified proof + kernel. Multi-month, research.** Entire ladder
   greenfield.
6. **Full string theory. Month+.** Bounded, BV-lowered, ≤16 bytes; no variable
   concat/substr/replace/symbolic-index/regex from text.
7. **Quantifier instantiation maturity. Month+.** Finite-domain only; no
   production trigger selection; no quantified LIA/LRA.
8. **SMT-LIB command-surface completeness. Weeks.** Missing declare-sort/
   define-sort, reset, echo, get-assignments, get-proof, full set-option.
9. **Nonlinear maturity. Multi-month.** Sound-incomplete; no CAD for decidable
   sub-fragments.
10. **FP/string `unsat` assurance & broader oracle cross-checking. Ongoing.** FP/
    string `unsat` is replay-blind; the strongest public bench ran oracle-disabled.

**Bottom line:** Destination (1) — a broad, evidence-backed decidable+arithmetic
foundation — is genuinely built and the ledger is honest and golden-tested.
Destinations (2) Z3-class performance and (3) Lean-checkable proofs are both early;
the two load-bearing fronts are **A1 (measured performance)** and **B2 (reduction
certificates)**.
