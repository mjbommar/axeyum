# axeyum current-state audit (baseline captured 2026-07-10)

> **Superseded as a live parity summary (2026-07-21).** This remains a useful
> point-in-time inventory, but rapid work after July 10 invalidated several of
> its gap conclusions. Use the
> [current scoped parity analysis](../gap-analysis-z3-lean-2026-07-21.md), the
> [generated SMT-LIB/API conformance matrix](../generated/smtlib-api-conformance.md),
> and the
> [categorical-engine audit](../categorical-engine-depth-audit-2026-07-21.md)
> for planning decisions. In particular, Lean proof export/checking, warm array
> handling, theory combination, nonlinear CAD, and much of the command surface
> are no longer accurately described by the original snapshot below.

The baseline this plan starts from. Source of truth: `PLAN.md` history,
`crates/axeyum-solver/src/capabilities.rs` (golden-tested ledger), committed
`bench-results/`. The decision index now runs through ADR-0080; pure-Rust
default, Z3 a feature-gated oracle.

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
| QF_ABV / QF_UF / QF_AUFBV | validated | canonical e-graph/BV refinement + replay, including original array equalities, explanation-guarded base/store-parent select scheduling, same-search ROW plus dynamically appended UF/select/extensionality scalar interfaces, shared direct-symbol class models, Bool/BitVec component combinations, finite-scalar array-valued UF results with array-first/function-second projection, bounded structural store/ITE/constant class equations, retained scalar-keyed warm array-result parents, and projection equality/exact structural diff witnesses (ADR-0071–0089); eager certifying fallback; direct equal-array select congruence checked in-tree/Carcara/Lean (ADR-0075); broader UNSAT DRAT **modulo trusted reduction** |
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
differential validation. Narrow zero-trust exceptions are tracked per query;
ADR-0075's direct equal-array select-congruence artifact is one such exception,
while ROW/diff-witness and general array elimination remain ledgered.

## Eager vs lazy/incremental
**Eager / one-shot (certifying fallback):** arrays (`abv.rs`, read-over-write+
Ackermann), UF (Ackermann),
LIA/LIRA (bit-blast to fixed width), datatypes, FP, strings, and the whole
`check_with_all_theories` pipeline.
**Genuinely incremental:** `IncrementalBvSolver` (`incremental.rs`) — warm AIG +
warm CNF over a persistent SAT solver, push/pop via selectors, learned clauses
retained; BMC/symexec ride it.
**Genuinely lazy (DPLL(T)-style):** canonical `CdclT` drives EUF, LIA/LRA,
UFBV, and bounded ABV/AUFBV interfaces; arrays over Bool/BitVec components use candidate-guided select,
ROW, and equality/diff instances, original equality atoms on live `EufTheory`,
explanation-guarded base/store-parent merge scheduling, and majority-default
direct-symbol/application-result class models, with violated local ROW sites
inserted permanently inside the same canonical search. Exact array-ITE equality
decomposition and bounded store/ITE/constant realization close structural total-
model gaps without changing observed reads (ADR-0071–0085).
`dpll_t.rs`/`dpll_lia.rs` remain arithmetic fallbacks and
`lazy_bv.rs` drops heavy mul/div gadgets. The warm path admits a bounded symbolic
array/UF slice and retains store/constant/ITE read owners plus candidate-
triggered exact transitive summaries in its persistent CNF (ADR-0086/0087).
Scalar-keyed array-valued UF applications also retain private array owners,
conditional read congruence, and full-value result projection (ADR-0088). The
warm path now merges projection-owned positive equality and gives top-level
structural disequality one exact private diff witness (ADR-0089), realizes
positive structural equality through private owners (ADR-0090), and keeps nested
Boolean array relation atoms warm through candidate-sensitive private flags
(ADR-0091). Direct finite-array UF parameters also stay warm through relation-
flag guarded key congruence and full-value key projection (ADR-0092), and
supported store/constant/array-ITE structural UF parameters retain scalar
dependencies plus structural owner realization before full-value projection
(ADR-0093). The solver still rebuilds for general deferred theories, including
nested array-valued application keys.

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

## Current gap routing (replaced 2026-07-21)

Do not use the original July 10 top-ten list to estimate present distance from
Z3 or Lean. The checked replacement separates three different targets:

1. **Scoped solver parity:** substantial across the 24-logics/992-file tracked
   corpus, with zero recorded oracle disagreements, but not a claim of Z3-wide
   coverage or production depth.
2. **Proof compatibility:** a real Lean-checkable SMT proof lane now exists; the
   remaining work is certificate coverage, trusted-reduction shrinkage, kernel
   profile hardening, and integration—not a green-field Lean exporter.
3. **Product compatibility:** the 30-row command/API inventory shows broad
   parsing and direct helper coverage, but no ordered interactive textual
   session result stream. That session contract is the next P4.4 architecture
   task.

The highest current gaps are production-scale performance and robustness,
missing or trusted reduction certificates, the ordered SMT-LIB session runner,
Lean ecosystem/kernel-profile integration, and measured deployment properties.
Full parity with either Z3 or Lean remains an intentionally rejected monolithic
milestone: those systems expose different categories of functionality, so each
claim needs a named surface, corpus, checker, and exit criterion.
