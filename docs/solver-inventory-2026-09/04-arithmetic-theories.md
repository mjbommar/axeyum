# Arithmetic theories: LRA, LIA, NRA, NIA, difference logic, and the CDCL(T) loop — inventory (2026-09-09)

Scope: the arithmetic half of `crates/axeyum-solver` — the CDCL(T)/DPLL(T)
engines (`cdclt.rs`, `native_cdclt.rs`, `dpll_t.rs`, `dpll_lia.rs`), the exact
simplex and LRA stack (`simplex.rs`, `lra.rs`, `lra/warm.rs`, `lra_online.rs`,
`lra_theory.rs`, `lra_route.rs`, `uflra_online.rs`), the LIA stack (`lia.rs`,
`lia_online.rs`, `lia_theory.rs`, `lia_gcd.rs`, `lia_counters.rs`,
`uflia_online.rs`, `uflia_interface.rs`, `int_real_relax.rs`), the eleven
nonlinear files (`nia_*`, `nra_*`), difference logic (`dl_online.rs`), the
model-checking routes built on arithmetic (`bmc.rs`, `imc*.rs`, `pdr*.rs`), the
integer proof reconstructors (`int_reconstruct.rs` + submodules), and the
numeric kernel crate `crates/axeyum-arith`. Base commit `ea8515407`. Route
SELECTION belongs to lane L3 and the proof/evidence story to lane L8; both are
cross-referenced, not duplicated. Interpolation files (`lia_interpolant*.rs`,
`lra_interpolant*.rs`, `alethe_lra.rs`) are named only where they consume these
solvers.

**Feature baseline.** Every `axeyum-solver` module below is declared inside the
single `full_modules!()` macro (`crates/axeyum-solver/src/lib.rs:70`, invoked at
`lib.rs:251-252`) under `#[cfg(feature = "full")]`, and `full` is not in
`default = ["qfbv"]` (`crates/axeyum-solver/Cargo.toml:40`). That is assumed
throughout and **not repeated per row**. `FEATURE-GATED` below means a gate that
is *not* `full`: `z3`, `bench-internals`, or a nested `#[cfg]`. `axeyum-arith` is
unconditional and has no features of its own.

## Summary

- **Two CDCL(T) drivers exist and both are live.** `cdclt.rs` (4,176 LOC) is the
  generic one; `native_cdclt.rs` (738 LOC) is a bridge that runs the same
  `TheorySolver` on `axeyum-cnf`'s proof-producing core. Since plan slice S7b,
  **LRA, LIA, difference logic, EUF and strings go through the native core**
  (`lra_theory.rs:363`, `lia_theory.rs:219`, `dl_online.rs:2279`,
  `euf_egraph.rs:1259`, `string_theory.rs:1069`) and therefore can emit the
  ADR-1704 two-stream artifact. **`uflra_online`, `uflia_online`, `ufbv_online`
  and `qinst_egraph` still call `CdclT` directly** (`uflra_online.rs:1354`,
  `uflia_online.rs:1819`, `ufbv_online.rs:1386`, `qinst_egraph.rs:3250`), and
  `cdclt.rs` emits no proof at all — so a `QF_UFLRA`/`QF_UFLIA` `unsat` reaches
  the front door with an empty trust slot by construction
  (`evidence.rs:2669-2673` names exactly those three routes).
- **The simplex is Dutertre–de Moura general simplex over exact rationals with
  δ-relaxation for strict rows** (`simplex.rs:1-4`, `:41-43`). The shipped
  entering rule is **not** Bland — it is fill-in minimising
  (`PivotPolicy::new`, `simplex.rs:176`), with Bland as a per-call fallback once
  `bland_threshold = 1_000` repeated leaving variables is crossed
  (`simplex.rs:139-150`). Bland is what recovers termination; `MAX_PIVOTS =
  2_000_000` (`simplex.rs:81`) and `MAX_TABLEAU_CELLS = 4_000_000`
  (`simplex.rs:74`) are the deterministic belts.
- **LIA is decided by three layered engines, not one**: a system-level
  Diophantine/gcd refuter (`lia_gcd.rs:39`, `:66`), a bounded Gomory fractional
  cut round (`lra.rs:2710`), then branch-and-bound (`lra.rs:2266`) — in that
  order (`decide_int_constraints`, `lra.rs:1913`). It is **not complete**: B&B
  degrades to `Unknown` at `MAX_LIA_BNB_NODES = 50_000` with no clock and
  `20_000_000` with one (`lra.rs:1706`, `:1717`), and the Boolean-structured
  loop caps at `MAX_DPLL_ROUNDS = 10_000` (`dpll_lia.rs:44`).
- **Of the eleven nonlinear files, four are search and six are pure certificate
  producers; one (`nia_square.rs`) is both.** The certificate producers are
  wired from a *different* front door than the deciders: search reaches
  `auto.rs`, certificates reach `evidence.rs::produce_evidence`
  (`evidence.rs:3489`). `nra_real_root.rs` (8,207 LOC) is the real decision
  engine — Sturm chains plus recursive N-variable CAD, all exact.
- **No float touches any arithmetic verdict.** `grep -c 'f64\|f32'` is 0 across
  all eleven `nia_*`/`nra_*` files and across all of `crates/axeyum-arith/src`;
  the positive control (`cdclt.rs:282` `VSIDS_DECAY: f64`) confirms the pattern
  fires. Floats appear in this area only as VSIDS activity and telemetry.
- **`pdr_lia.rs` (1,106 LOC) and `imc_lia.rs` (665 LOC) are public API with no
  in-workspace production caller.** `horn.rs`'s `dispatch` explicitly declines
  `Int` state (`horn.rs:687-690`), so only `Real` and `BitVec`/`Bool` reach an
  engine. Both are still `pub` through `lib.rs:778` and `lib.rs:788`.
- **`check_with_int_blasting` (`lia.rs:45`) has no caller inside the
  workspace outside tests**; `check_auto`'s width ladder
  (`auto.rs:7202`) blasts directly.
- **Oracle-differential coverage is uneven.** Thirteen `z3`-gated arithmetic
  differential fuzzes exist. **Difference logic has none**, and there is no
  pure-`QF_LIA` differential fuzz (LIA is covered only inside
  `nia_differential_fuzz.rs` and via `uflia_differential_fuzz.rs`).
- **Div/mod by a constant zero is an uninterpreted fresh variable, not a fixed
  convention** (`crates/axeyum-rewrite/src/int_divmod.rs:11-16`), and the
  degenerate case *is* generated by a dedicated fuzz that draws a zero divisor
  ~37 % of the time and guarantees at least one per instance
  (`tests/qf_nia_divmod_const_differential_fuzz.rs:77`, `:357`).
- **`axeyum-arith` is reached from the solver transitively, not directly.**
  `axeyum-solver/Cargo.toml` does not name it; `axeyum-ir` does
  (`crates/axeyum-ir/Cargo.toml:21`), and `axeyum_ir::Rational`'s big-value pool
  is `axeyum_arith::big::BigRational` (`crates/axeyum-ir/src/rational.rs`). So
  it *is* on the soundness path, one crate removed.
- Reachability tally for this lane: **31 WIRED, 3 TEST-ONLY, 2 NO PRODUCTION
  CALLER FOUND, 2 FEATURE-GATED (`bench-internals`)**. Detail per row below.

## Inventory

### CDCL(T) / DPLL(T) engines

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `CdclT` generic driver | `src/cdclt.rs` | 4176 | Online CDCL(T) over the Boolean skeleton; 1-UIP over a mixed clause DB, Luby restarts, LBD reduction, phase saving, deadline + step budget. Emits **no proof**. | WIRED (4 routes) + FEATURE-GATED(`bench-internals`) for the public path | `uflra_online.rs:1354`, `uflia_online.rs:1819`, `ufbv_online.rs:1386`, `qinst_egraph.rs:3250`; `pub` re-export only via `lib.rs:271` `bench_internals` |
| `native_cdclt` bridge | `src/native_cdclt.rs` (+`native_cdclt/tests.rs` 849) | 738 | Adapts a `TheorySolver` to `axeyum_cnf::theory::NativeTheory` (`native_cdclt.rs:332`) and runs the proof-producing core; publishes the ADR-1704 `TheoryRefutation` on a thread-local with an "exactly one refutation" guard. | WIRED (5 routes) | `lra_theory.rs:363`, `lia_theory.rs:219`, `dl_online.rs:2279`, `euf_egraph.rs:1259`, `string_theory.rs:1069` |
| `dpll_t` — offline LRA lazy-SMT | `src/dpll_t.rs` | 1772 | Boolean abstraction → `SatBvBackend` → conjunctive `check_with_lra` → blocking clause. Also probes the online CDCL(T) route first (`dpll_t.rs:384`). Carries `LraDpllRefutation`. | WIRED | `nra.rs:40` (`check_with_lra_dpll_within`), public at `lib.rs:668` |
| `dpll_lia` — offline LIA/LIRA lazy-SMT | `src/dpll_lia.rs` | 5895 | Same shape for integers, and for the mixed `QF_LIRA` case where Int and Real atoms are theory-checked independently (no interface equalities — they share no sort). Carries `ArithDpllRefutation` (`dpll_lia.rs:161`). | WIRED | `auto.rs:2742`, `:2907`, `:3027` (route `lia-dpll`); `auto.rs:4600` (route `lira-dpll`) |
| `TheorySolver` trait | `src/euf_egraph.rs:67` | — | `assert`/`push`/`pop`/`propagate` + ADR-1701 additions `final_check`, `propagate_into`, `explain`, `take_new_atoms`, `engine_counters`. | WIRED | see implementor list below |

`TheorySolver` implementors that are arithmetic (production, not test):
`LraTheory` (`lra_online.rs:1181`), `CdcltLraTheory` (`lra_theory.rs:169`),
`LiaTheory` (`lia_online.rs:1731`), `CdcltLiaTheory` (`lia_theory.rs:113`),
`DlTheory` (`dl_online.rs:1649`), `CombinedIncremental` (EUF+LRA,
`combined_theory.rs:697`), `CombinedIncrementalLia` (EUF+LIA,
`combined_theory_lia.rs:827`). Non-arithmetic implementors (`EufTheory`,
`StringTheory`, `CombinedUfbvTheory`) belong to other lanes.

### Simplex and LRA

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| General simplex | `src/simplex.rs` | 2855 | Dutertre–de Moura; `feasible` one-shot + `Incremental` warm engine; Farkas multipliers on infeasible; ADR-1702 `wide_*` promotion contained by `narrow` (`simplex.rs:420`). | WIRED + FEATURE-GATED(`bench-internals`) for the public path | `lra.rs:594`; `Incremental` driven by `LraTheory`; `pub` only via `lib.rs:272` |
| Conjunctive LRA + the offline LIA engines | `src/lra.rs` | 4185 | Fourier–Motzkin `check_with_lra` with a self-checked `FarkasCertificate`; **also hosts** `tighten_strict_integer_constraints` (`:1861`), `lia_gomory_cuts` (`:2710`), `lia_branch_and_bound` (`:2266`), `decide_int_constraints` (`:1913`), `lia_simplex_capped` (`:1991`). | WIRED | `auto.rs:39`, `dpll_t.rs`, `dpll_lia.rs:36-39` |
| Warm LIA front end | `src/lra/warm.rs` (+`lra/warm/tests.rs` 691) | 769 | Per-literal collection cache + trail-delta-updated constraint system that reproduces the cold path's system **column-for-column** (`warm.rs:41-58`). Despite living under `lra/`, it warms the **integer** decider. | WIRED | `lia_online.rs:81` (`use crate::lra::warm::{LiaWarmPolicy, WarmLiaDecider, ambient_lia_warm_policy}`); public at `lib.rs:1214` |
| Online LRA theory | `src/lra_online.rs` | 6017 | `LraTheory` (`:1181`), the Tseitin `Encoder`, atom collection, Farkas-minimal conflict cores, bound propagation, `check_qf_lra_online`. | WIRED | via `lra_theory.rs`; public at `lib.rs:679` |
| CDCL(T) LRA adapter | `src/lra_theory.rs` | 932 | `CdcltLraTheory` guarantees the driver's trigger-literal invariant; `check_qf_lra_online_cdclt`. Budget is bytes (ADR-1752), calibrated to reproduce the old `MAX_ONLINE_LRA_ATOMS = 1_024`. | WIRED | `dpll_t.rs:384` |
| LRA route policy | `src/lra_route.rs` | 235 | Policy object with a `legacy()` arm: skeleton encoding, fall-through on cheap decline, and `SIMPLEX_FIRST_AT_CONSTRAINTS = 256` (`:60`). | WIRED | `dpll_t.rs:383`, `lra.rs:594`, `lra_online.rs:3823` |
| `QF_UFLRA` online combination | `src/uflra_online.rs` | 2360 | EUF + LRA under one `CdclT` trail with interface equalities. **Runs `CdclT` directly, so no ADR-1704 artifact.** | WIRED | `auto.rs:4208` (route `uf-arith-online`) |

### LIA

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| Bounded int-blast | `src/lia.rs` | 155 | `check_with_int_blasting`: blast Int→BV at width `B`, replay as exact integers. `unsat` is always downgraded to `Unknown` (`lia.rs:15-17`). | **TEST-ONLY** inside the workspace (public API) | only callers: `tests/lia.rs:25`, `tests/integer_scenarios.rs:32`. `auto.rs`'s ladder (`auto.rs:7202`) blasts directly. |
| Online LIA theory | `src/lia_online.rs` | 3588 | `LiaTheory` (`:1731`), re-decides via the warm offline decider; eager or ADR-1701-deferred feasibility. | WIRED | via `lia_theory.rs`; public at `lib.rs:670` |
| CDCL(T) LIA adapter | `src/lia_theory.rs` | 594 | `CdcltLiaTheory` + `check_qf_lia_online_cdclt`; drives the **native** core. | WIRED | `dpll_lia.rs:568`, `dpll_lia.rs:1453` |
| Diophantine / gcd refuters | `src/lia_gcd.rs` | 1108 | `prove_lia_unsat_by_gcd` (`:39`, single equation, `gcd(aᵢ) ∤ b`) and `prove_lia_unsat_by_diophantine` (`:66`, fraction-free integer row reduction over a system), plus a self-validating certified variant (`:108`). Sound-incomplete, silent when it cannot refute. | WIRED | `auto.rs:2732`, `auto.rs:2821` (route `lia-diophantine`) |
| LIA telemetry | `src/lia_counters.rs` (+`lia_counters/tests.rs` 459) | 1052 | Opt-in, clock-free counters for Gomory rounds/cuts/pivots, B&B nodes, warm-cache hit rate. **No decision logic.** | WIRED (instrumentation) | `lra.rs:1934-1944`, `lra.rs:2723` |
| `QF_UFLIA` online combination | `src/uflia_online.rs` | 2920 | EUF + LIA equality sharing under one `CdclT` trail. **Runs `CdclT` directly → no ADR-1704 artifact.** | WIRED | `auto.rs:4210`, `abv.rs:2197` |
| UFLIA interface policy | `src/uflia_interface.rs` | 927 | Interface-pair proposal policy + counters; `MAX_INTERFACE_PAIRS = 64` (`:157`) caps shared-term case splits. | WIRED | `uflia_online.rs:97`, `combined_theory_lia.rs:58` |
| Int→Real relaxation | `src/int_real_relax.rs` | 287 | Reinterprets an integer query over ℝ so NRA sign rules can refute it; sound for `unsat` only; aborts wholesale on `div`/`mod`/`abs`/`bv2nat`. | WIRED | `auto.rs:5359` (route `int-real-relax`); also `reconstruct/arithmetic/ordered_ring.rs:826` |

### Nonlinear — the search/certificate split

| Component | Path | LOC | Search or certificate | Reachability | Evidence |
|---|---|---|---|---|---|
| `nia_linearize.rs` | 2406 | **SEARCH** — `check_with_nia` (`:1350`) returns `Option<CheckResult>`; product abstraction + sign/monotonicity lemmas + variable-divisor Euclidean linearization over the integer DPLL(T). Never returns `Unknown` itself: a stalled loop is a *decline* (`:1673-1678`). | WIRED | `auto.rs:5390` (route `nia-linearize`); `has_nonlinear_int_product` at `auto.rs:1730`, `dpll_lia.rs:543` |
| `nia_square.rs` | 928 | **BOTH** — `decide_int_square_constraint_explained` (`:327`) is a search decider; `int_quadratic_negative_discriminant_refutation` (`:418`) + checker (`:452`) is a certificate pair. | WIRED (both) | search `auto.rs:5307` (route `nia-square`); certificate `evidence.rs:3385`, checker `evidence.rs:1193` |
| `nia_univariate_cert.rs` | 785 | **CERTIFICATE** — `int_univariate_refutation` (`:192`) + `check_int_univariate_refutation` (`:315`). No decide return type. | WIRED (evidence front door only) | `evidence.rs:3359`, checker `evidence.rs:1200` |
| `nra.rs` | 2016 | **SEARCH** — `check_with_nra` (`:261`): linear abstraction + replay + sign/zero product lemmas + McCormick envelopes + spatial B&B. Delegates the linear residual to `dpll_t::check_with_lra_dpll_within` (`nra.rs:40`). | WIRED | `auto.rs:4696` (route `nra`), `auto.rs:4371` (route `uf-nra`), `int_real_relax.rs:120`, `evidence.rs:3142` |
| `nra_even_power.rs` | 408 | **CERTIFICATE**, used as a cheap decider — `nra_even_power_refutation` (`:37`) + `certificate_refutes_its_assertion` (`:86`). | WIRED (twice) | pre-check inside `check_with_nra` (`nra.rs:313`) and directly in dispatch at `auto.rs:2372` (route `nra-even-power`); evidence `evidence.rs:3224` |
| `nra_fbbt.rs` | 1097 | **HYBRID** — `derive_bounds` (`:562`) is bound-propagation search; `verify` (`:436`) is a Farkas checker gating every derived bound before it reaches a verdict. | WIRED, internally only | `nra_real_root.rs:8126` (`derive_bounds`), consumed at `nra_real_root.rs:413`. No top-level route label. Public coverage helper at `lib.rs:1240`. |
| `nra_handelman_cert.rs` | 1451 | **CERTIFICATE** — `handelman_refutation` (`:866`) + `check_handelman_refutation` (`:339`). | WIRED (evidence) | `evidence.rs:3304`, checker `evidence.rs:1221` |
| `nra_monomial_bound_cert.rs` | 1123 | **CERTIFICATE** — `monomial_bound_refutation` (`:471`) + checker (`:730`). | WIRED (evidence + Lean reconstruction) | `evidence.rs:3251`, `reconstruct.rs:3279` |
| `nra_product_cert.rs` | 696 | **CERTIFICATE** — degree-2 Positivstellensatz; `real_product_refutation` (`:372`) + checker (`:447`). | WIRED (evidence + reconstruction) | `evidence.rs:3275`, `reconstruct.rs:1862` |
| `nra_real_root.rs` | 8207 | **SEARCH** (plus an internal SOS certificate) — `decide_real_poly_constraint` (`:336`); Sturm chains (`isolate_roots → isolate_roots_sturm → sturm_isolate_rec`, `:93-94`), 2-var resultant elimination (`:2683`), recursive N-variable CAD (`decide_strict_cad_nvar` `:4331`, `decide_nonstrict_cad_nvar` `:4479`). `integer_algebraic_refutation` (`:6174`); `sos_refute_with_certificate` (`:6927`). | WIRED | `auto.rs:4646` (route `nra-real-root`), `dpll_t.rs:616`; `integer_algebraic_refutation` at `auto.rs:1180`, `:1562` |
| `nra_zero_product_cert.rs` | 528 | **CERTIFICATE** — monomial divisibility; `real_zero_product_refutation` (`:229`) + checker (`:268`). | WIRED (evidence + reconstruction) | `evidence.rs:3324`, `reconstruct.rs:1869` |

Search: 4 files (`nia_linearize`, `nra`, `nra_real_root`, plus `nia_square`'s
decider). Certificate: 6 files (`nia_univariate_cert`, `nra_even_power`,
`nra_handelman_cert`, `nra_monomial_bound_cert`, `nra_product_cert`,
`nra_zero_product_cert`). Hybrid: `nra_fbbt` (search gated by its own checker)
and `nia_square` (one file, two roles). **No `nia_*`/`nra_*` file has zero
callers.**

The frontier baselines for this area: `BASELINE_NRA_DEGREE = 40`
(`tests/progress_frontier.rs:210`) and `BASELINE_NIA_UNSAT = 40` (`:221`). The
`nia_unsat` capability comes from `decide_bounded_int_blast` in `auto.rs`
(`progress_frontier.rs:216-219`), **not** from `nia_linearize` or `nia_square` —
worth knowing given the 17-point regression CLAUDE.md records, because the
frontier family and the file most people would edit are not the same code.

### Difference logic

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `dl_online` | `src/dl_online.rs` (+`dl_online/tests.rs` 1277) | 2338 | Incremental **Cotton–Maler** negative-cycle detection over a maintained feasible potential π (`:35-42`), driven as a `TheorySolver` (`DlTheory`, `:1649`). Entry `try_check_qf_dl` (`:2189`). Runs the native core (`:2279`). Unsat carries a unit-multiplier `FarkasCertificate` from `cycle_certificate` (`:1219`), verified before it is accepted. | WIRED | `auto.rs:4440` inside `dispatch_difference_logic`, invoked at `auto.rs:4592` (route `dl-online`) |

### Model checking on arithmetic

| Component | Path | LOC | Entry | Reachability | Evidence |
|---|---|---|---|---|---|
| `bmc.rs` | 1149 | `bounded_model_check` (`:131`), `prove_safety_k_induction` (`:335`) | BMC: **WIRED** to a consumer crate. k-induction: **TEST-ONLY**. | BMC at `crates/axeyum-verify/src/bmc.rs:260`, plus internal use at `pdr.rs:783`, `imc.rs:224`. `prove_safety_k_induction` searched with `grep -rn "prove_safety_k_induction(" --include=*.rs .`: every hit outside its own definition is under `tests/`. Engine: `IncrementalBvSolver` (`bmc.rs:210`). |
| `imc.rs` | 553 | `prove_safety_imc` (`:140`) | WIRED | `horn.rs:722` (BitVec/Bool fallback after PDR). Engine: `check_auto` (`imc.rs:62`). |
| `imc_lra.rs` | 647 | `prove_safety_imc_lra` (`:169`) | WIRED | `horn.rs:713` (Real fallback). |
| `imc_lia.rs` | 665 | `prove_safety_imc_lia` (`:191`) | **NO PRODUCTION CALLER FOUND** | `grep -rn "prove_safety_imc_lia" crates/ --include=*.rs` returns only its own file, `lib.rs:778`/`:1165` re-exports, `capabilities.rs:2123`, and `tests/imc_lia.rs`. `horn.rs:687-690` declines `Int` state outright. Shipped public API, dead from the inside. |
| `pdr.rs` | 987 | `prove_safety_pdr` (`:258`), `prove_safety_pdr_certified` (`:292`) | WIRED | `horn.rs:719`. Engine: `IncrementalBvSolver` (`pdr.rs:804`) + `check_auto` for the trusted 3-check gate (`verify_invariant`, `pdr.rs:835`). |
| `pdr_lra.rs` | 1082 | `prove_safety_pdr_lra` (`:205`) | WIRED | `horn.rs:709`. |
| `pdr_lia.rs` | 1106 | `prove_safety_pdr_lia` (`:225`) | **NO PRODUCTION CALLER FOUND** | Same search shape as `imc_lia`: only `lib.rs:788`/`:1264`, `capabilities.rs:2106`, `tests/pdr_lia.rs`. |

These are **not research prototypes in the sense of being unfinished** — PDR
really does produce an inductive invariant and re-verify it with three
`check_auto` calls before returning `Safe` (`pdr.rs:835`, `:873`), and IMC really
does run an interpolation fixpoint (`imc.rs:252`) and gate it the same way. They
are prototypes in the sense of **reach**: `solve_horn`, the one dispatcher that
drives six of the seven, has no caller outside `tests/horn.rs` and
`tests/api_namespaces.rs`. `bounded_model_check` is the only one with a
non-test consumer (`axeyum-verify`).

### Integer proof reconstruction (see lane L8 for the wider evidence story)

Every submodule below consumes an already-found refutation and produces a **Lean
kernel term** (`ExprId`, `infer`-checked and `def_eq`-compared to `False`,
`int_reconstruct.rs:19-20`) and/or a self-contained Lean 4 module string. The
certificate structs are the *inputs*, not the outputs.

| Component | Path | LOC | Produces | Reachability |
|---|---|---|---|---|
| `int_reconstruct.rs` | 3495 | ADR-0042 Diophantine/integer-infeasibility → `False` over the `IntPrelude` | WIRED — `reconstruct.rs` dispatcher |
| `affine_growth.rs` | 467 | `reconstruct_int_affine_growth_to_lean_module` (`:46`) → `String` | WIRED — `reconstruct.rs:2751` |
| `counterexample_cover.rs` | 1465 | `reconstruct_quantified_counterexample_cover_to_lean_module` (`:1385`) → `String` | WIRED — `reconstruct.rs:2777` |
| `diophantine.rs` | 794 | `reconstruct_diophantine_proof` (`:27`) → `ExprId`; `..._to_lean_module` (`:73`) → `String` | WIRED — `evidence.rs:2054`, `:3440`, `reconstruct.rs:2864`, `uflia_interpolant.rs:390` |
| `equality_partition.rs` | 1200 | `reconstruct_single_pivot_equality_partition_to_lean_module` (`:1159`) | WIRED — `reconstruct.rs:2761` |
| `euclidean_residue.rs` | 354 | `reconstruct_int_euclidean_residue_to_lean_module` (`:35`) | WIRED — `reconstruct.rs:2741` |
| `inequality.rs` | 1201 | `reconstruct_int_inequality_proof` (`:1118`) → `ExprId`; `..._to_lean_module` (`:1136`) | WIRED — `reconstruct.rs:2870`, `uflia_interpolant.rs:395` |

### `crates/axeyum-arith` — the numeric kernel

| Module | LOC | Provides | Public types |
|---|---|---|---|
| `lib.rs` | 1857 | Dyadic floats, certified radix conversion, modular rings, trait scaffolding for polynomials/Hensel/algebraic numbers | `Round`, `Dyadic`, `Radix`/`RadixCertificate`, `MixedRadix*`, traits `Normalize`, `UnivariatePoly`, `FractionFree`, `ModularRing`, `HenselLift`, `AlgebraicNumber`, `BezoutCertificate`, `SturmCertificate`, `PowModCertificate`, `PlainModRing` |
| `big.rs` | 28 | The crate's single naming point for bignums; `scripts/check-arith-boundary.sh` fails the build if a crate names `num-bigint`/`num-rational` directly (`big.rs:9-10`) | re-exports `BigInt`, `BigUint`, `Sign`, `Integer`, `BigRational`, `One`, `Signed`, `ToPrimitive`, `Zero` |
| `rational.rs` | 612 | On-demand-normalized rational carrier: arithmetic that never calls gcd, plus a receipt of what one deferred reduction cost | `NormalizationReceipt`, `RawRational` |
| `upoly.rs` | 2013 | Univariate polynomials over ℤ/ℚ, fraction-free ops, extended Euclid/Bezout, Sturm chains, real-root isolation | `ZPoly`, `QPoly`, `PolyBezoutCertificate`, `PolyGcdCertificate`, `SturmChain`, `isolate_real_roots`, `count_real_roots*` |
| `hensel.rs` | 569 | Quadratic p-adic lifting of a simple root with a chain certificate | `HenselRoot`, `HenselCertificate`, `lift_root` (`:243`) |

Deps: only `num-bigint`, `num-rational`, `num-integer`, `num-traits`, all pure
Rust and WASM-safe (`crates/axeyum-arith/Cargo.toml:16-27`). Dependents:
`axeyum-ir` (`Cargo.toml:21`), `axeyum-cas` (`:24`), `axeyum-fp` (`:16`).
`axeyum-solver` does **not** depend on it directly — it goes through
`axeyum_ir::Rational` and `axeyum_ir::RealAlgebraic`, both of which use
`axeyum_arith::big::BigRational` internally.

## Data flow

**One CDCL(T) round, in call order** (generic driver; the native core mirrors it
through `NativeTheoryAdapter`):

1. `CdclT::solve` (`cdclt.rs:2227`) → `solve_inner` (`:2353`). Head of the loop:
   step-budget check, optional live-instrument mirror, `timed_out()`.
2. `CdclT::propagate` (`:2040`) — a fixpoint of two stages:
   a. `unit_propagate` (`:1140`) — two-watched-literal Boolean BCP. Each
      assignment goes through `assign` (`:1012`), which calls
      `TheorySolver::assert` (the ADR-1701 *cheap partial check*). An `Err(core)`
      here is a theory conflict.
   b. `theory_propagate` (`:1348`) — calls `register_new_atoms` (`:1335`,
      draining `take_new_atoms`) then `TheorySolver::propagate_into` into a
      driver-owned `PropagationQueue`. Each entailed literal is assigned with a
      reason clause built by `theory_reason_clause` (`:1470`); a deferred
      explanation handle is resolved later by `reason_for` (`:1310`) →
      `TheorySolver::explain`. The loop repeats until the trail stops growing.
3. On a conflict: `learn_and_backjump` (`:2065`) → `analyze_conflict` (`:1495`) —
   **1-UIP resolution over the mixed implication graph** (Boolean input clauses,
   theory conflict clauses `¬⋀core`, and theory reason clauses
   `¬reason ∨ lit` all live in one clause DB), then `minimize` (`:1652`) /
   `lit_redundant` (`:1702`), `backjump_level` (`:1747`), `backjump_to` (`:1759`,
   which calls `TheorySolver::pop` in lockstep), `alloc_clause` + `attach_clause`,
   and the UIP is enqueued with the learned clause as its reason. An empty
   asserting clause at level 0 is `Outcome::Unsat`; an unresolvable explanation
   handle is `Outcome::Unknown`, never an empty clause (`:2065-2090`).
4. If `pick_unassigned` (`:1931`, conflict-side VSIDS over an order heap with
   lowest-index tie-break) returns `None`, the assignment is **total** and
   `run_final_check` (`:2310`) calls `TheorySolver::final_check` — the ADR-1701
   *complete* check. `Sat` ends the search; `Conflict(explanation)` is resolved
   (`resolve_explanation`, `:1283`), backjumped to the trigger level, and fed
   back into `learn_and_backjump`; `Unknown` degrades the whole search.
   An empty core is treated as `Unknown`, explicitly so it cannot become a wrong
   `unsat` (`:2328-2332`).
5. Otherwise a decision: `decision_level += 1`, `TheorySolver::push`, assign the
   saved phase.

**LRA through that loop.** `LraTheory::assert` (`lra_online.rs:1192`) pushes the
atom's constraint(s) onto the live set; in eager mode it immediately re-decides
`feasibility()`, in deferred mode it only installs bounds and defers the simplex
to `final_check`. Conflict cores are the Farkas-participating subset of asserted
atoms (`rows_to_core`). `push`/`pop` snapshot the `(live, assigned_log)` lengths.

**Route entry for real queries.** `check_auto` has **no `lra` route label**:
a real query enters at `auto.rs:4696` as route `nra`, `nra::check_with_nra`
abstracts nonlinear products and hands the linear residual to
`dpll_t::check_with_lra_dpll_within`, which *first* probes
`lra_theory::check_qf_lra_online_cdclt` (`dpll_t.rs:384`) and only falls through
to the offline lazy-SMT loop on a structural or cheap decline
(`dpll_t.rs:402-414`). Inside the conjunctive decider, `lra.rs:594` consults
`lra_route::configured().simplex_first(n)` to decide whether the exact simplex
runs before Fourier–Motzkin.

**Route ladder for integer queries** (labels from `auto.rs` recorder sites):
`bv2nat-range` → `lia-diophantine` (`auto.rs:2821`) → `lia-simplex`
(`:2835`) → `lia-dpll` (`:2920`) for linear; and for nonlinear
`nia-square` (`:5307`) → `int-real-relax` (`:5365`) → `nia-linearize` (`:5390`)
→ `nia-bounded-blast` (`:5411`) → `cas-ideal-refuter` → `int-blast-ladder`
(`:7202`). `dl-online` (`:4451`) runs ahead of all of `lira-dpll`, the NRA
routes and the LIA-DPLL chain (`auto.rs:4592`).

## Entry points and public API

`lib.rs`'s `theories::arithmetic` facade (`lib.rs:666-678`) is the documented
surface: `check_with_arith_dpll`, `check_with_lia_dpll`, `check_with_lra_dpll`,
`DEFAULT_INT_WIDTH`, `check_with_int_blasting`, `LiaTheory`,
`check_qf_lia_online`, `check_qf_lia_online_cdclt`, `check_with_lia_simplex`,
`check_with_lra`, `check_with_lra_simplex`, `lra_unsat_core`, `LraTheory`,
`check_qf_lra_online` (`lib.rs:675`), `check_qf_lra_online_cdclt`, `check_with_nra`.
`theories::combination` (`lib.rs:725-737`) adds `check_qf_uflia_online`,
`check_qf_uflra_online` and the whole `TheorySolver` contract.
`theories::cdclt_diagnostics` (`lib.rs:745-748`) exposes
`TheoryLayerStatsGuard` / `last_theory_layer_stats`.
`verification::{transition_systems, imc, pdr, horn}` (`lib.rs:760-822`) exposes
all seven model-checking entry points.

Not on the facade, and reachable only through `check_auto`: `dl_online`,
`nia_linearize`, `nia_square`, `int_real_relax`, `nra_real_root`, and every
`*_cert` module (those reach the user through `evidence::produce_evidence`).

`bench_internals` (`lib.rs:269-280`, feature `bench-internals`, implies `full`)
is the only public path to `cdclt::{CdclT, Lit, Outcome}` and
`simplex::{Incremental, Rel, Status}`. Its existence is the sharpest available
statement of where the hot path is: those two modules are what
`benches/cdclt_propagate.rs` and `benches/simplex_pivot.rs` time.
`benches/dl_negative_cycle.rs` needs only `full` because it drives `check_auto`.

**One non-default environment lever in this area:** `AXEYUM_SIMPLEX_PIVOT`
(`simplex.rs:216-251`), read once into a `OnceLock` so determinism survives.
`bland` selects the pre-2026-09-08 rule; an integer sets `bland_threshold`; an
unrecognized value silently falls back to the default.

## Tests and gates

**`z3`-gated arithmetic differential fuzzes** (each compiles to zero tests
without `--features z3`; confirm a nonzero count):

| Suite | Gate line | Route |
|---|---|---|
| `qf_lra_differential_fuzz.rs` | `:22` `#![cfg(feature = "z3")]` | Boolean-structured `QF_LRA`, online CDCL(T) |
| `simplex_lra_fallback_differential.rs` | `:16` | `QF_LRA` simplex fallback past `MAX_FM_CONSTRAINTS` |
| `qf_uflra_differential_fuzz.rs` | `:21` | `QF_UFLRA` online Nelson–Oppen |
| `uflia_differential_fuzz.rs` | `:49` | `QF_UFLIA` |
| `nia_differential_fuzz.rs` | `:38` | `QF_NIA`/`QF_LIA` general |
| `qf_nia_divmod_const_differential_fuzz.rs` | `:35` | constant-divisor (incl. **constant zero**) `div`/`mod` |
| `qf_nia_divmod_var_differential_fuzz.rs` | `:31` | variable-divisor Euclidean `div`/`mod` |
| `qf_nia_bounded_product_differential_fuzz.rs` | `:41` | bounded product abstraction |
| `qf_nia_pow2_differential_fuzz.rs` | `:29` | power-of-two special case |
| `qf_nia_iand_differential_fuzz.rs` | `:23` | `iand` bounded blast |
| `nra_differential_fuzz.rs` | `:26` | `QF_NRA` CAD/algebraic grid |
| `qf_ufnra_differential_fuzz.rs` | `:24` | `QF_UFNRA` eager Ackermann + NRA |
| `quantified_uflia_model_finder_differential_fuzz.rs` | `:32` | quantified UFLIA MBQI sat side |

**Arithmetic routes with NO oracle-differential coverage — findings:**

1. **Difference logic (`QF_IDL`/`QF_RDL`).** No `z3`-gated fuzz exists anywhere
   under `crates/axeyum-solver/tests/`. Searched `grep -ln 'feature = "z3"'
   crates/axeyum-solver/tests/*.rs` and cross-checked the filename list; the only
   DL-named test file is `difference_logic_lean_content.rs`, which is
   `full`-only and is about certificate rendering, not a verdict comparison.
   `dl_online` is a *complete* decider on its fragment, produces `unsat`, and is
   run **ahead of** every other arithmetic route in `check_auto`
   (`auto.rs:4592`) — an unoracled complete decider in front position.
2. **Pure `QF_LIA`.** There is no `qf_lia_differential_fuzz.rs`. Coverage is
   indirect: `nia_differential_fuzz.rs` generates linear instances incidentally,
   and `uflia_differential_fuzz.rs` covers LIA only under UF.
3. **`int_real_relax.rs` and `lia_gcd.rs`** have no fuzz aimed at them; both
   are sound-`unsat`-only refuters run early in the ladder, so a bug in either
   is a wrong `unsat` on the first route that answers.
4. **`bmc`/`imc`/`pdr`** have no differential coverage of any kind (their
   `Safe` verdicts are re-verified in-tree by `check_auto`, which is the same
   engine, not an independent one).

**Oracle-free (`full`-only) arithmetic suites:** `lia.rs`, `lia_dpll.rs`,
`lia_gomory.rs`, `lia_simplex.rs`, `lia_online.rs`, `lra.rs`, `lra_online.rs`,
`cdclt_lia_online.rs`, `cdclt_lra_online.rs`, `cdclt_online.rs`, `dpll_t.rs`,
`nia_*.rs` (11 files), `nra*.rs` (9 files), `imc*.rs`, `pdr*.rs`,
`int_divmod.rs`, `nia_divmod_linearize.rs`, `uf_arith_dispatch_differential.rs`
(an internal A-vs-B differential against the eager Ackermann baseline, no
oracle), `math_resource_{lia,lra}_routes.rs`, and the ratchet
`progress_frontier.rs` (families `lia_cuts` = 26, `nra_degree` = 40,
`nia_unsat` = 40).

**Div/mod by constant zero (CLAUDE.md's `a946f925`).** The convention now lives
in `crates/axeyum-rewrite/src/int_divmod.rs`. For `c ≠ 0` the Euclidean pair is
an exact equisatisfiable linear elimination; for `c = 0` the term maps to a
**fresh unconstrained variable**, never a fixed value, and the module doc names
the regression and its fix inline (`int_divmod.rs:11-16`: "the P0 regressed by
`a946f925`, fixed by `52f3b1d1`"). Pairwise congruence lemmas over distinct
zero-divisor dividends are emitted up to `MAX_CONGRUENCE_GROUPS = 48`
(`int_divmod.rs:485`); above that, `ZeroDivisorCongruence::Omitted` sets
`sat_transfers() == false` (`:104-113`) and `auto.rs`'s `guard_zero_divisor_sat`
(`auto.rs:2760-2780`) downgrades the `Sat` to `Unknown`. `unsat` transfers at
every group count, since the lemmas only enlarge the model set.
The degenerate case **is** generated: `tests/qf_nia_divmod_const_differential_fuzz.rs`
draws a zero constant divisor about 37 % of the time (`:77`) and guarantees at
least one constant-zero divisor per instance (`:357`), and its own doc states it
is the gate that would have caught the P0 (`:7-9`). It is `z3`-gated (`:34-35`).

## Doc drift

No single existing document inventories this area, so drift was checked against
the two in-tree authorities that make claims about it.

1. **`crates/axeyum-solver/src/support_matrix.rs:238` says of `QF_LRA`:
   "exact-rational simplex is complete for QF_LRA".** The source is narrower in
   three ways the row does not qualify. `simplex.rs` declines to
   `SimplexOutcome::Unknown` when a feasible point or a Farkas multiplier does
   not fit `i128` after `narrow` (`simplex.rs:420`, doc at `:29-36`), when the
   pivot budget `MAX_PIVOTS = 2_000_000` is exhausted (`:81`), and
   `Incremental::new` refuses a tableau above `MAX_TABLEAU_CELLS = 4_000_000`
   (`:74`). Above that the caller keeps whatever engine it had. `lra.rs`'s own
   module doc is the accurate statement: "complete for the admitted conjunctive
   `QF_LRA` shape when its explicit resource guards and current `i128`-backed
   rational range are not exceeded" (`lra.rs:10-13`). The support row is
   defensible about the *algorithm* and misleading about the *implementation*.
2. **`docs/research/09-decisions/adr-1710-...md:82` says "No existing crate
   depends on it in this slice", and the ADR is still `Status: proposed`
   (line 5), dated 2026-09-05.** Three crates now depend on `axeyum-arith`:
   `crates/axeyum-ir/Cargo.toml:21`, `crates/axeyum-cas/Cargo.toml:24`,
   `crates/axeyum-fp/Cargo.toml:16`. The migration named in the ADR has at
   least partly landed and the ADR status has not moved with it.
3. **`support_matrix.rs:243-257` (difference logic) is accurate** and worth
   quoting as a model: it says the conjunctive `unsat` carries a checked
   `FarkasCertificate` while the Boolean-structured case "is a resolution over
   theory lemmas and stays a bare unsat, so the row is partial-trust". That
   matches `dl_online.rs:1219` + `evidence.rs:2644-2652` exactly. No drift.
4. **No drift found** between `support_matrix.rs:209-231` (`QF_LIA`) and the
   source: it already names Diophantine refutation, branch-and-bound and Gomory
   cuts, and already says the route degrades to `unknown` on the node budget.

## Gaps and open questions

- **I could not determine what fraction of real queries actually reach the
  simplex versus Fourier–Motzkin**, only that `lra_route.rs:60` sets the
  crossover at 256 constraints on the strength of a 2026-09-08 measurement over
  22 files. Determining it needs a `--trace` run over a corpus with the pivot
  counters armed; I did not run anything.
- **The `bench-internals` promotion of `CdclT`/`Incremental` to `pub` is a
  standing hazard I did not test.** The modules stay crate-private, but the
  types are `pub`, so a stray `pub use` elsewhere would silently widen the API.
  A `cargo public-api` diff or a rustdoc check would settle it; both need a
  build. `[unverified]`
- **`imc_lia.rs` and `pdr_lia.rs` (1,771 LOC together) have no production
  caller, and I could not tell whether that is deliberate staging or an
  oversight.** `horn.rs:687-690` gives a reason ("an `Int` real-relaxation
  cannot be verified over ℤ in this slice"), which reads as deliberate — but
  the two engines are fully implemented and tested, so the gap is in the
  dispatcher, not the engines. Whether the `Int` decline is still necessary now
  that `int_real_relax.rs` exists is a question for whoever owns `horn.rs`.
- **I did not verify the LOC-to-behaviour ratio in `nra_real_root.rs`
  (8,207 LOC, the largest file in the area).** Agent-read evidence identifies
  Sturm chains, resultant elimination and recursive N-variable CAD with cited
  lines, but I did not read the whole file; a claim about what fraction of it is
  reachable from `decide_real_poly_constraint` would need a coverage run.
- **The absence of a difference-logic oracle fuzz is a gap I can name but not
  price.** `dl_online` is run first, is complete on its fragment, and produces
  `unsat` — so the population it decides never reaches another engine that could
  contradict it. Writing `qf_dl_differential_fuzz.rs` in the shape of
  `qf_lra_differential_fuzz.rs` would close it; nothing structural prevents it.
- **`check_with_int_blasting` is public API with only test callers.** Whether it
  should be deprecated in favour of the internal width ladder, or the ladder
  should route through it, is a design question I am flagging rather than
  answering.
