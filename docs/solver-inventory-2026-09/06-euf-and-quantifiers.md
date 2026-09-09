# EUF, e-graphs, and quantifier reasoning — inventory (2026-09-09)

Scope: EUF core (`euf.rs`, `euf_egraph.rs`, `bool_euf.rs`, `uf_arith.rs`,
`uf_fmf.rs`, `qinst_egraph.rs`), the standalone `crates/axeyum-egraph`
congruence-closure crate, the 37-file `quant_*.rs` family in
`crates/axeyum-solver/src/`, and adjacent reasoning entry points
(`nat_induction.rs`, `horn.rs`, `abduct.rs`, `hypothesis_min.rs`, `mbp.rs`,
`mbqi_model_finder.rs`). Base commit `ea8515407`. Alethe/proof-text emission
(`quant_alethe.rs`, `skolem_alethe.rs`) belongs to lane L8 and is
cross-referenced by name only; `crates/axeyum-rewrite/src/quantifiers.rs`
(finite-domain quantifier expansion) belongs to lane L2 and is
cross-referenced for the skolemization pipeline question.

**Baseline note (per coordinator calibration):** every file in this lane's
scope is declared inside the `full_modules!()` macro
(`crates/axeyum-solver/src/lib.rs:70`, invoked at `lib.rs:252`), gated
`#[cfg(feature = "full")]`. None of it exists in the default (`qfbv`) build.
This is stated once and not repeated per row; the reachability tables below
classify WIRED / TEST-ONLY / NO CALLER FOUND *within* the `full` baseline, and
reserve FEATURE-GATED for a gate other than `full` (there are none found in
this lane's scope — no nested `z3`/`bench-internals` cfg was found inside any
file listed here).

## Summary

- The `quant_*.rs` family is **37 files**, not ~45 as the brief estimated:
  9 `_search`/`_cert` pairs (18 files) that follow the naming convention
  exactly, 8 more `_cert` files with no `_search` counterpart by name, and 11
  files that are neither suffix. Every `_search` file's matching `_cert`
  exists (`grep -n` confirms all 9); the interesting finding is the reverse
  direction — 8 cert-only files, and of those, 3 are genuinely self-contained
  decision+certificate procedures called directly from `qinst_egraph.rs`
  rather than from a peer search module, and 4 more pair with a *search* file
  that does not share their name prefix at all (`quant_guarded_int` /
  `quant_finite_cert`, `quant_bool_model_sat` / `quant_bv_instance_set_cert`,
  `qinst_egraph` / `quant_instance_set_cert`, `mbqi_model_finder` /
  `quant_uf_model_sat_cert`). A table built only from the `_search`/`_cert`
  suffix convention misses these four pairs entirely.
- Reachability: of the 37 `quant_*.rs` files, **36 are WIRED** to the
  dispatcher (`auto.rs`) or to the evidence/reconstruction pipeline
  (`evidence.rs`, `reconstruct.rs`), each with a cited caller site below.
  **1 file, `quant_sat_certificates.rs`, is data-only** (certificate struct
  definitions with no decision logic) and has no direct caller of its own —
  it exists purely so `Model` does not depend on five checker modules
  (`quant_sat_certificates.rs:1-9`); its types are consumed via re-export.
  No `quant_*.rs` file in this lane's scope came back NO CALLER FOUND.
- Outside `quant_*.rs`: `check_with_function_elimination` (the Ackermann
  elimination entry point in `euf.rs:336`) has **no caller in `src/` outside
  its own file and `lib.rs`'s public re-export** — only integration tests
  (`tests/functions.rs`, `tests/function_scenarios.rs`,
  `tests/ackermann_unsat_proofs.rs`, `tests/euf_egraph_diff.rs`,
  `tests/ufbv_online_differential_fuzz.rs`) call it. It is public API and
  test-covered but is not on the path a query submitted through
  `auto::check_with_quantifiers`/the SMT-LIB front door actually takes.
  `horn.rs` and `abduct.rs` are similar: dedicated integration test suites
  (`tests/horn.rs`, `tests/abduct.rs`) exist and the functions are public API,
  but no internal dispatcher call was found. `hypothesis_min.rs` has neither
  a dispatcher caller nor a dedicated integration test file — only its own
  `#[cfg(test)]` module (`hypothesis_min.rs:421`).
- Congruence closure: there is **exactly one** implementation,
  `crates/axeyum-egraph` (a dependency-free, single-file, 2,675-line crate;
  ADR-0032). `euf_egraph.rs` is a thin SMT-facing wrapper around it
  (`use axeyum_egraph::{EGraph, ...}`) and is the WIRED route for pure QF_UF
  congruence reasoning. `euf.rs` is a **different, non-e-graph technique**:
  Ackermann-congruence elimination to `QF_BV`/arithmetic (ADR-0013, predates
  ADR-0032) — it has no union-find of its own and does not import
  `axeyum_egraph`. The two do not "disagree" because they are not both
  invoked on the same query as competing checkers; `auto.rs` dispatches
  `euf_egraph`'s online CDCL(T) route first (`auto.rs:3780`) and only falls
  through to `euf.rs`'s `check_with_uf_arithmetic` (`auto.rs:3862`) for the
  UF+arithmetic combination the e-graph route alone does not decide.
- `qinst_egraph.rs` is genuinely huge: **13,058 lines**, by far the largest
  file in this lane's scope (next largest is `euf_egraph.rs` at 4,063). It is
  the e-matching / quantifier-instantiation driver, built directly on
  `axeyum_egraph::{EGraph, EMatchIndex, Pattern, Substitution}`
  (`qinst_egraph.rs:35`), and it inlines three of the standalone cert modules
  (`quant_affine_growth_cert`, `quant_nested_xor_cert`, `quant_residue_cert`)
  as special-shape fast paths during its instantiation loop.
- Skolemization runs conditionally, mid-pipeline, not up front:
  `auto.rs::prove_unsat_by_ematching` (`auto.rs:8652`) tries top-level
  trigger instantiation first (`instantiate_with_triggers`, from
  `axeyum-rewrite`, lane L2's crate); only if a residual quantifier survives
  does it call `quant_skolemize::skolemize_assertions_with_layout`
  (`auto.rs:8674`), specifically to expose *nested* universals to the
  top-level-only trigger matcher, then retries instantiation
  (`auto.rs:8685`) before falling through to the `qinst_egraph` loop
  (`auto.rs:8734`). This is the opposite order from "preprocess by
  skolemizing, then dispatch": here skolemization is itself a fallback step
  inside quantifier dispatch, not a `axeyum-rewrite` preprocessing pass.
- What decides today vs. returns `unknown`, by fragment: finite-domain
  Bool/BV universals are complete via rewrite-level expansion
  (`check_with_quantifiers`, lane L2's territory) plus the sat/vacuous/valid
  passes in this lane; bounded/guarded `Int` universals decide via
  `quant_guarded_int`+`quant_finite_cert`; several *exact* shapes (affine
  growth, nested XOR, Euclidean residue, Fourier-Motzkin over reals/closed
  ints) decide unconditionally when the shape matches and decline otherwise;
  general infinite-domain quantification is `unknown`-by-default, moved only
  by e-matching (`qinst_egraph`) or MBQI-style finite model search
  (`mbqi_model_finder` + `quant_uf_model_sat_cert`, pure-UF only, SAT-only).
  Detail in the "Decided vs. unknown" table below.
- `mbp.rs` (model-based projection) and `uf_fmf.rs` (finite model finding)
  are both WIRED, not prototypes: `mbp::mbp_lia`/`mbp::mbp_lra` are called
  from MBQI candidate repair (`auto.rs:7636-7637`), and
  `uf_fmf::find_uf_finite_model` is called twice from the quantified-UF
  SAT ladder (`auto.rs:351`, `auto.rs:433`).
- A large, dated (2026-09-09) inline comment block at `auto.rs:8695-8720`
  gives measured numbers directly relevant to Q3: on the scored UF corpus,
  126 of 159 declined-status files hit the residual-quantifier fallthrough,
  the skolemizer reaches all of them, and 26 of 32 sampled files in
  `bench-results/parity-losses-20260908/UF.txt` stop at the e-matching
  loop's ground-term budget ceiling, not at a shape limitation — worth
  reading verbatim if scoping future quantifier work.

## Inventory

### quant_*.rs — the search/cert pairing table (37 files)

Convention-matched pairs (`_search` name and `_cert` name share a prefix):

| Search | Cert | Search called from | Cert called from (internal to search) | What the cert asserts |
|---|---|---|---|---|
| `quant_bv_alternation_search.rs` (201) | `quant_bv_alternation_cert.rs` (237) | `auto.rs:80` | `quant_bv_alternation_search.rs:12` | Source-bound counterexample for BV quantifier alternation (ADR-0124) |
| `quant_bv_conjunctive_search.rs` (147) | `quant_bv_conjunctive_cert.rs` (312) | `auto.rs:96` | `quant_bv_conjunctive_search.rs:10` | A found BV conjunctive-universal instance replays against source |
| `quant_bv_model_sat_search.rs` (409) | `quant_bv_model_sat_cert.rs` (822) | `auto.rs:71,897` | `quant_bv_model_sat_search.rs:12` | `QuantifiedBvModelSatCertificate`/`Proof` for a BV model-sat verdict |
| `quant_bv_paired_exists_search.rs` (235) | `quant_bv_paired_exists_cert.rs` (564) | `auto.rs:88` | `quant_bv_paired_exists_search.rs:10` | Paired-existential BV transfer witness replay |
| `quant_closed_counterexample_search.rs` (143) | `quant_closed_counterexample_cert.rs` (96) | `evidence.rs:2800`, `reconstruct.rs:2636,2655` | `quant_closed_counterexample_search.rs:10` | Closed-form universal counterexample replay |
| `quant_eq_partition_search.rs` (222) | `quant_eq_partition_cert.rs` (250) | `auto.rs:606` | `quant_eq_partition_search.rs:8` | Finite equality-partition quantifier refutation (ADR-0101) |
| `quant_guard_vacuity_search.rs` (47) | `quant_guard_vacuity_cert.rs` (114) | `auto.rs:66` | via re-exported `check_quantified_guard_sat` (`quant_guard_vacuity_search.rs:5`) | ADR-0122 guarded quantified SAT certificate replay |
| `quant_negated_exists_search.rs` (103) | `quant_negated_exists_cert.rs` (137) | `auto.rs:92` | `quant_negated_exists_search.rs:10` | Negated-existential witness replay |
| `quant_vacuous_exists_counterexample_search.rs` (95) | `quant_vacuous_exists_counterexample_cert.rs` (185) | `auto.rs:84` | `quant_vacuous_exists_counterexample_search.rs:10` | Vacuous-`exists` universal counterexample replay |

Note on `quant_guard_vacuity_search`: the direct `grep` for
`quant_guard_vacuity_cert::` inside it returns 0 hits because the call goes
through a crate-root re-exported name (`check_quantified_guard_sat`,
imported at `quant_guard_vacuity_search.rs:5`) rather than the fully
qualified module path — the same pattern recurs for `quant_sat_cert`'s
`check_model` below. A naive module-qualified grep undercounts wiring in
this family; confirmed by reading the `use` line, not by the module-path
grep alone.

Cert-only files (no `_search`-suffixed sibling), with their actual
counterpart identified by reading each file's own doc comment and imports:

| Cert file | LOC | Real search-side counterpart | Counterpart evidence | Called from |
|---|---|---|---|---|
| `quant_finite_cert.rs` | 1450 | `quant_guarded_int.rs` (different name) | `quant_finite_cert.rs:13,63,1129,1239` all cross-reference `crate::quant_guarded_int`; `config_registry.rs:7041` notes the two share `RANGE_SIZE_CAP` "deliberately... so a proof is producible whenever this pass decides to expand" | `evidence.rs:116` (checker), also emits Alethe (`prove_finite_int_quant_unsat_alethe`, `prove_finite_int_quant_unsat_uf_alethe` — overlaps lane L8's territory) |
| `quant_bv_instance_set_cert.rs` | 166 | `quant_bool_model_sat.rs` (different name) | `quant_bv_instance_set_cert.rs:1` (ADR-0134); `quant_bool_model_sat.rs:23` imports it directly | `quant_bool_model_sat.rs:23,44` → `auto.rs:76` |
| `quant_instance_set_cert.rs` | 805 | `qinst_egraph.rs` (different name, e-matching driver) | `quant_instance_set_cert.rs:1-9` names `qinst_egraph` explicitly as the search side | `evidence.rs:488,1289,2734,2747`; `qinst_egraph.rs:842,844,3758` |
| `quant_uf_model_sat_cert.rs` | 1047 | `mbqi_model_finder.rs` (different name, MBQI) | `quant_uf_model_sat_cert.rs:1-4`: "MBQI search is not evidence... independently checks one exact source assertion" | `auto.rs:7975,8199` |
| `quant_affine_growth_cert.rs` | 300 | none — self-contained | `quant_affine_growth_cert.rs:13`: "does not call the instantiation search" | `qinst_egraph.rs:2497`, `evidence.rs:1780,2701`, `reconstruct.rs:2749`, `int_reconstruct/affine_growth.rs:6` |
| `quant_nested_xor_cert.rs` | 274 | none — self-contained | no search cross-reference in file | `qinst_egraph.rs:2468`, `evidence.rs:1789,2706`, `reconstruct.rs:1714,2729`, `int_reconstruct.rs:49` |
| `quant_residue_cert.rs` | 309 | none — self-contained | `quant_residue_cert.rs:19`: "independently of the counterexample-instantiation search in `qinst_egraph`" | `qinst_egraph.rs:2482`, `evidence.rs:1771,2684`, `reconstruct.rs:2739`, `int_reconstruct/euclidean_residue.rs:4` |
| `quant_sat_cert.rs` | 795 | none — self-contained (data split into `quant_sat_certificates.rs`) | `quant_sat_cert.rs:16-21` | `check_model`/`check_model_with_assignment` used at `auto.rs:357,404,439,1350,1510` via crate-root re-export (not `quant_sat_cert::` qualified) |

"Neither" files (no `_search`/`_cert` suffix at all):

| File | LOC | Role | Reachability |
|---|---|---|---|
| `quant_alethe.rs` | 1100 | Alethe proof emission for quantifier unsat | Lane L8 — not analyzed here |
| `quant_bool_model_sat.rs` | 1601 | Search+check combined pass: erases quantifiers to a ground Boolean candidate, then proves every original assertion against it (own doc: "Search erases... checker below proves") | WIRED, `auto.rs:76` |
| `quant_counterexample_cover.rs` | 347 | Checked finite counterexample covers for positive Bool/Int universals (ADR-0108) | WIRED, `evidence.rs:1506,2949`, `quant_bool_model_sat.rs:27`, `int_reconstruct/counterexample_cover.rs:7` |
| `quant_exists_witness.rs` | 913 | Bounded ∀∃ decision by Skolem-witness synthesis, sat-side | WIRED, `auto.rs:308` |
| `quant_fourier_motzkin.rs` | 1523 | Single-variable real Fourier-Motzkin elimination for a top-level universal | WIRED, `auto.rs:651-686` (6 call sites) |
| `quant_guarded_int.rs` | 401 | Guarded-finite-`Int` universal expansion — the search side of `quant_finite_cert` (see above) | WIRED, `auto.rs:42` |
| `quant_sat_certificates.rs` | 168 | Certificate **data only** (no logic), split out so `Model` doesn't depend on 5 checker modules | Not directly called; consumed via `pub use` re-export by `Model` and `quant_sat_cert.rs:21` |
| `quant_skolemize.rs` | 1003 | Polarity-aware NNF + Skolemization + prenexing, mid-pipeline fallback (see Data flow) | WIRED, `auto.rs:8674,8677` |
| `quant_unsat_universal.rs` | 343 | Unsatisfiable-universal detection (single linear body, non-vacuous, non-cancelling case) | WIRED, `auto.rs:621` |
| `quant_vacuous_universal.rs` | 450 | Vacuous-universal elimination (bound var doesn't affect body) | WIRED, `auto.rs:593` |
| `quant_valid_universal.rs` | 230 | Valid-universal elimination (sat-side validity of universal closure) | WIRED, `auto.rs:571` |

### EUF core

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `euf.rs` | `crates/axeyum-solver/src/euf.rs` | 3204 | Ackermann-congruence elimination of UF to `QF_BV`/arithmetic (ADR-0013); `check_with_uf_arithmetic`/`check_with_uf_arithmetic_lazy` are the eager/lazy combination routes | WIRED (combination routes) / **NO internal caller for `check_with_function_elimination`** | `auto.rs:3862` calls `check_with_uf_arithmetic`; `check_with_function_elimination` (`euf.rs:336`) has zero callers in `src/` outside its own file — confirmed by `grep -rn "check_with_function_elimination(" crates/axeyum-solver/src`, only `lib.rs` re-export and `tests/*.rs` hit |
| `euf_egraph.rs` | `crates/axeyum-solver/src/euf_egraph.rs` | 4063 | SMT-facing wrapper over `axeyum_egraph::EGraph`: online CDCL(T) (`check_qf_uf_online_cdclt`), offline (`check_qf_uf_with_config`), congruence-only refutation (`prove_unsat_by_congruence`) | WIRED | `auto.rs:3780` (online, tried first), `auto.rs:3808` (offline fallback) |
| `bool_euf.rs` | `crates/axeyum-solver/src/bool_euf.rs` | 334 | Exhaustive/online EUF refutation specialized to Boolean-sorted terms | WIRED (evidence/reconstruction path only, not `auto.rs` dispatch) | `evidence.rs:1666,1675,3019,3026,4258,4261`; `reconstruct.rs:1824,1826`; `reconstruct/direct.rs:523,546` |
| `uf_arith.rs` | `crates/axeyum-solver/src/uf_arith.rs` | 174 | Congruence-refutation certificate mixing UF with arithmetic (`uf_arith_congruence_refutation`) | WIRED (evidence/reconstruction path only) | `evidence.rs:1684,3033,4264`; `reconstruct.rs:1828`; `reconstruct/direct.rs:570` |
| `uf_fmf.rs` | `crates/axeyum-solver/src/uf_fmf.rs` | 1520 | Finite model finding for pure-UF quantified SAT queries (upward search over per-sort carrier bound `k`, `BitVec(w)` encoding) | WIRED | `auto.rs:351` (probe), `auto.rs:433` (full) |
| `qinst_egraph.rs` | `crates/axeyum-solver/src/qinst_egraph.rs` | 13058 | E-matching / quantifier-instantiation driver on `axeyum_egraph::{EGraph, EMatchIndex, Pattern, Substitution}`; also inlines 3 standalone shape-specific cert checks | WIRED | `auto.rs:41` (import), `auto.rs:8734` (`prove_quantified_unsat_via_egraph`, final fallback in the ematching ladder) |

### crates/axeyum-egraph — the congruence-closure crate

Single file, `crates/axeyum-egraph/src/lib.rs`, 2675 lines, ADR-0032, no
`axeyum-*` dependencies of its own. Optional dependency of `axeyum-solver`,
pulled in only by `full` (`axeyum-solver/Cargo.toml:53`, `dep:axeyum-egraph`
inside the `full = [...]` feature list).

| Component | Role | Evidence |
|---|---|---|
| `EGraph` (`lib.rs:353`) | Core structure: hash-consed e-node creation (`add`, `lib.rs:922`), path-compressing union-find (`find`, `lib.rs:956`), deferred-merge cascade (`merge`, `lib.rs:987`), backtrackable (`push`/`pop`, `lib.rs:997,1058`) | ADR-0032 |
| `EMatchIndex`/`Pattern`/`Substitution` (`lib.rs:166`) | E-matching machinery: `ematch`, `ematch_many`, `ematch_many_indexed` (`lib.rs:563-631`) | Consumed by `qinst_egraph.rs:35` |
| `explain`/`explain_steps` (`lib.rs:1303,1330`) | Proof-forest explanation for a derived equality | ADR-0032's "explanation / proof forest" follow-up task |
| `check_congruence` (`lib.rs:1496`) | Independent brute-force congruence re-validator, separate from the incremental structure | ADR-0032: "an **independent congruence checker**" |

### Related reasoning entry points

| Component | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|
| `nat_induction.rs` | 331 | `prove_by_nat_induction`: induction-based decision attempt | WIRED | `auto.rs:769` |
| `horn.rs` | 2449 | `solve_horn`: Horn-clause system solving | Public API + dedicated test suite, **no internal dispatcher caller found** | `lib.rs` re-export (`#[doc(hidden)]`); `tests/horn.rs` |
| `abduct.rs` | 693 | `abduct`: abductive hypothesis search | Public API + dedicated test suite, **no internal dispatcher caller found** | `lib.rs` re-export; `tests/abduct.rs` |
| `hypothesis_min.rs` | 749 | `minimize_hypotheses`/`split_goal_and_minimize`: hypothesis-set minimization | Public API only, **no internal caller and no dedicated integration test found** | `lib.rs:1158-1161` re-export (not `#[doc(hidden)]`); only own `#[cfg(test)]` at `hypothesis_min.rs:421`; searched `tests/*hypothesis*` — no file, and grepped `tests/abduct.rs`/`tests/horn.rs` for the function names — no hits |
| `mbp.rs` | 1487 | `mbp_lia`/`mbp_lra`: model-based projection (Cooper/Omega, Loos-Weispfenning) | WIRED | `auto.rs:7636-7637` |
| `mbqi_model_finder.rs` | 941 | Search-side MBQI candidate generation, feeding `quant_uf_model_sat_cert` for checking | WIRED | `auto.rs:7649,7652,8120,8179,8183` |

## Data flow

Two independent quantifier ladders exist in `auto.rs`, tried in sequence by
the caller (`check_with_quantifiers`, `auto.rs:7288`):

1. **Standalone-universal fast passes** (all sat/unsat-side, applied to a
   top-level `∀x. body` before any instantiation): `quant_valid_universal`
   (`auto.rs:571`) → `quant_vacuous_universal` (`auto.rs:593`) →
   `quant_unsat_universal` (`auto.rs:621`) → `quant_eq_partition_search`
   (`auto.rs:606`) → `quant_fourier_motzkin` (`auto.rs:651-686`, real/int
   closed/valid/open-gap variants) → `quant_exists_witness` (`auto.rs:308`,
   ∀∃ Skolem witness) → the `quant_bv_*` family (alternation, conjunctive,
   paired-exists, model-sat, negated-exists, vacuous-exists-counterexample,
   `auto.rs:66-97`).
2. **`prove_unsat_by_ematching`** (`auto.rs:8652`), the fallback ladder for
   whatever the fast passes decline:
   `instantiate_with_triggers` (top-level trigger E-matching, from
   `axeyum-rewrite`, `auto.rs:8661`) → if a residual quantifier remains,
   `quant_skolemize::skolemize_assertions_with_layout` (`auto.rs:8674`,
   NNF + Skolemize existentials + prenex/hoist survivors, so *nested*
   universals become visible to the top-level-only trigger matcher) →
   retried `instantiate_with_triggers` on the skolemized set (`auto.rs:8685`)
   → `qinst_egraph::prove_quantified_unsat_via_egraph` (`auto.rs:8734`), the
   incremental e-graph multi-pattern instantiation loop, run **unsat-only**
   on the skolemized set (not unioned with the originals — `auto.rs`'s inline
   comment records this was measured strictly worse).

Inside the `qinst_egraph` loop itself, three shape-specific standalone cert
modules are tried as fast paths before falling back to general e-matching:
`quant_affine_growth_cert::int_affine_growth_refutation`
(`qinst_egraph.rs:2497`), `quant_nested_xor_cert::int_nested_xor_refutation`
(`qinst_egraph.rs:2468`), `quant_residue_cert::int_euclidean_residue_refutation`
(`qinst_egraph.rs:2482`).

For pure QF_UF (no quantifiers), the ladder in `auto.rs` around line 3760 is:
`euf_egraph::check_qf_uf_online_cdclt` (online CDCL(T) on the backtrackable
e-graph, `auto.rs:3780`) → `dispatch_ufbv_online` (scalar UFBV combination,
`auto.rs:3799`) → `euf_egraph::check_qf_uf_with_config` (offline enumeration,
`auto.rs:3808`) → (implied, not re-verified here) eager Ackermann elimination
via `euf.rs`'s `check_with_uf_arithmetic` for the UF+arithmetic combination
case (`auto.rs:3862`).

## Entry points and public API

Everything in this lane's scope is `pub use`-exported from `lib.rs` inside
the `#[cfg(feature = "full")]` block (lines given per-component above), so an
external consumer with `--features full` can call `check_with_uf_arithmetic`,
`check_with_function_elimination`, `solve_horn`, `abduct`, `minimize_hypotheses`,
`prove_by_nat_induction`, `mbp_lia`/`mbp_lra`, and the `quant_*` cert-checker
functions directly. Some re-exports are `#[doc(hidden)]` (`horn`, `imc`,
`imc_lia` — `lib.rs:1157,1162,1164`), signaling they are public-but-unadvertised
surface. `axeyum-egraph`'s `EGraph`/`ENodeId`/`EMatchIndex`/`Pattern` types are
not re-exported through `axeyum-solver`; a consumer who wants the raw e-graph
must depend on `axeyum-egraph` directly.

## Tests and gates

- Dedicated integration tests exist for nearly every `quant_*_cert` module
  under `crates/axeyum-solver/tests/`: `evidence_quant_affine_growth.rs`,
  `evidence_quant_bv_conjunctive_instance.rs`, `evidence_quant_bv_instance_set.rs`,
  `evidence_quant_bv_paired_exists.rs`, `evidence_quant_cert.rs`,
  `evidence_quant_closed_counterexample.rs`, `evidence_quant_eq_partition.rs`,
  `evidence_quant_negated_exists.rs`, `evidence_quant_nested_xor.rs`,
  `evidence_quant_residue_cert.rs`, `evidence_quant_vacuous_exists_counterexample.rs`,
  `evidence_finite_quant_uf_cert.rs`, plus shape-level tests
  (`quant_fourier_motzkin.rs`, `quant_guarded_int.rs`, `quant_int_fm_closed.rs`,
  `quant_int_fm_valid.rs`, `quant_int_open_gap.rs`, `quant_vacuous.rs`,
  `quant_valid_universal.rs`, `quant_unsat_universal.rs`,
  `quant_exists_witness.rs`, `quant_bool_model_sat.rs`, `quant_bv_model_sat.rs`,
  `quant_sat_certificate.rs`, `quant_counterexample_cover.rs`), Lean-export
  variants (`quant_affine_growth_lean.rs`, `quant_closed_counterexample_lean.rs`,
  `quant_eq_partition_lean.rs`, `quant_nested_xor_lean.rs`,
  `quant_residue_lean.rs`), user-trigger tests (`quantifier_user_triggers.rs`,
  `quantifiers.rs`), and differential fuzzes (`quantified_bv_differential_fuzz.rs`,
  `quantified_uf_fmf_differential_fuzz.rs`,
  `quantified_uflia_model_finder_differential_fuzz.rs`). All of these are
  `full`-gated by inheritance — none were checked for the
  `#![cfg(feature = "full")]` inertness trap named in CLAUDE.md, and per that
  trap this must be confirmed with `--features full`, not assumed
  `[unverified]`.
- `abduct.rs` and `horn.rs` each have exactly one top-level integration test
  file (`tests/abduct.rs`, `tests/horn.rs`) and no internal dispatcher
  wiring — coverage exists, dispatch wiring does not.
- `crates/axeyum-egraph/src/lib.rs` has its own `#[cfg(test)] mod tests`
  at line 1559; not further broken down here — brief did not ask for a
  sub-inventory of that module and it is a single file.
- No test file matching `*hypothesis*` was found under
  `crates/axeyum-solver/tests/` (`find crates/axeyum-solver/tests -iname
  "*hypothesis*"` returns nothing).

## Doc drift

`docs/plan/track-2-theories/P2.6-quantifiers.md` carries a "Current
checkpoint (2026-07-14)" section describing the e-graph instantiation loop,
trigger inference, MBQI/MBP, and CEGQI as "live" — consistent with what this
inventory found wired today, no contradiction. But it predates by nearly two
months the dated, more specific commentary now sitting inline in
`auto.rs:8695-8720` (2026-09-09) about *why* the UF corpus's residual bucket
declines: the plan doc does not mention the measured 126-of-159 residual-quantifier
figure, the skolemizer reaching every one of them, or the ground-term budget
ceiling being the actual stopping point on 26 of 32 sampled files. This is
not a false statement in the plan doc, just a materially more precise,
more recent account that lives in a code comment instead of the plan
document — worth pulling forward if `P2.6-quantifiers.md` is next
refreshed.

`docs/plan/status/116-quantifier-triggers.md` (2026-08-21) states user
`:pattern` triggers are "threaded parse → IR → the E-matching loop" and
`:weight` is declined; this inventory did not re-derive that path (out of
the brief's file list — the parser/IR layer is outside
`crates/axeyum-solver/src/quant_*.rs` and the EUF files named in scope) so it
is reported here as an unverified but plausible claim, not confirmed
independently.

No drift found against `docs/research/09-decisions/adr-0032-egraph-crate.md`
— its description of `axeyum-egraph` as the shared, dependency-free
congruence-closure keystone with union-find, deferred-merge cascade,
explanation, and an independent checker matches the current
`crates/axeyum-egraph/src/lib.rs` exactly (component table above).

## Gaps and open questions

- `check_with_function_elimination`'s lack of a dispatcher caller was
  confirmed by exhaustive `grep -rn` across `crates/axeyum-solver/src`
  (returns only its own definition and doc comments) and `lib.rs`'s
  re-export; it was **not** confirmed with a build (per the method brief's
  no-`cargo` rule), so `[unverified]`: whether some other crate
  (`axeyum-bench`, `axeyum-scenarios`) calls it directly was not checked —
  only `axeyum-solver/src` and `axeyum-solver/tests`.
- `--features full` was assumed to compile cleanly and the listed
  `full`-gated tests were assumed to run with a nonzero test count; per
  CLAUDE.md's documented inertness trap for this exact feature flag, this is
  `[unverified]` and should be confirmed with
  `cargo test -p axeyum-solver --features full --test <name>` showing a
  nonzero count before trusting the "tests exist" claims above as "tests
  run and pass".
- The claim that `euf_egraph`'s online and offline routes and `euf.rs`'s
  Ackermann route "never both run on the same query" rests on reading the
  `auto.rs:3760-3862` control flow (each route returns early on `Sat`/`Unsat`
  and only falls through on `Unknown`) rather than on tracing every possible
  config/feature combination — a config that disables early return was not
  searched for.
- `quant_finite_cert.rs`'s primary public functions
  (`prove_finite_int_quant_unsat_alethe`,
  `prove_finite_int_quant_unsat_uf_alethe`) are Alethe-proof-text producers,
  which puts part of this file's public surface inside lane L8's stated
  scope even though the file itself was named in this lane's brief. Flagged
  here rather than resolved — the decision logic (`RANGE_SIZE_CAP`-bounded
  finite conjunction) is this lane's; the Alethe emission is L8's.
- `docs/plan/status/116-quantifier-triggers.md`'s `:pattern` → IR → matcher
  path was not independently traced (parser and IR layers are out of this
  lane's file list); flagged as the one claim in the Doc drift section that
  is reported rather than verified.
