# Post-processing: models, proofs, certificates, and evidence — inventory (2026-09-09)

Everything the solver produces **after** a verdict: models and their replay,
the `Evidence` envelope and its checkers, Alethe emission, reconstruction into
Lean-kernel terms, interpolation, the bit-blast miter, CAS certificates, and
the trust ledger. Paths covered: `crates/axeyum-solver/src/{model,
counterexample, faithfulness, evidence, trust, certify, proof, *_alethe,
reconstruct*, lex_reconstruct*, int_reconstruct*, word_reconstruct,
regex_reconstruct, *interpolant*, bitblast_miter, cas_certificate,
cas_poly}.rs`, plus `crates/axeyum-cnf/src/{alethe,drat,drat_backward,lrat,
interpolant}.rs` and the crates `axeyum-machine-evidence`, `axeyum-verify`,
`axeyum-verify-macros`. The Lean kernel crate itself
(`crates/axeyum-lean-kernel`, ~806k lines) is **out of scope**: only the
interface `axeyum-solver` calls is inventoried. Base commit `ea8515407`.
Source-reading only — nothing here was built or run, and claims that would
need a build are marked `[unverified]`.

**Feature baseline.** Almost all of this area is declared inside the
`full_modules!()` macro at `crates/axeyum-solver/src/lib.rs:70`, invoked at
`lib.rs:251-252` under `#[cfg(feature = "full")]`. `full` is therefore the
assumed baseline for every table below and is **not** repeated per row; the
`FEATURE-GATED` label is reserved for gates that are not `full` (`z3`,
`bench-internals`, `batsat-reference`). The default-profile split is measured
separately in [§2](#2-what-the-default-qfbv-build-can-produce), because for
this lane it is a real finding rather than boilerplate.

## Summary

- **The evidence system is large and mostly honest about itself.** `Evidence`
  has **66 variants** (`evidence.rs:371-838`), each with a `kind_label`
  (`:927`) and a certificate-specific re-checker (`recheck_certificate`,
  `:1097-1375`). Re-validation is three-valued on purpose —
  `EvidenceCheck::{Verified, NothingToCheck(reason), Failed}` (`:328-334`) —
  so "nothing to check" cannot read as a pass (ADR-0384).
- **The key gap is `Evidence::Unsat(None)`, the bare uncertified `unsat`.**
  It is produced at 8 distinct non-test sites in `evidence.rs` and is what the
  NRA route (`:3144`), the timeout-budgeted fallback (`:3814`), the string
  front door (`:4119`), and the general `solve` fallback return. Its label is
  `"unsat-uncertified"` (`:937`) and `check_outcome` reports
  `NothingToCheck(UncertifiedUnsat)` (`:290-296`). Nothing is fabricated —
  but for these routes the project's "trusted small checking" identity does
  not hold, and the code says so.
- **`sat` model replay is NOT universal and NOT centralized.** There is no
  single choke point. The default `QF_BV` backend replays unconditionally
  (`sat_bv_backend.rs:2387` → `replay_model`, `:2424`), and about a dozen
  other routes replay in their own code (`abv.rs:242`, `aufbv.rs:112`,
  `combined.rs:222`, `dpll_t.rs:1033`, `lia.rs:115`, `preprocess.rs:192`,
  `nia_linearize.rs:1557`, `nra.rs:271`, `ufbv_online.rs:3136`,
  `array_fifo.rs:206`, `uflra_online.rs:938`, `quant_bv_model_sat_search.rs:294`).
  The `full`-profile canonical checker `check_model` (`quant_sat_cert.rs:408`)
  is a **consumer-facing API**, not something the solver runs on every `sat`.
  The `z3` oracle strategy's replay is `#[cfg(feature = "z3")]`
  (`strategy.rs:192-232`). See [§3](#3-sat-model-replay-where-it-actually-runs).
- **Alethe: 12 emitter modules, 11,733 lines, one in-tree checker.**
  `axeyum_cnf::check_alethe` / `check_alethe_with`
  (`crates/axeyum-cnf/src/alethe.rs:937,956`) natively handles ~29 rules
  including three **axeyum-internal** array rules Carcara does not know
  (`read_over_write`, `read_over_write_same`). Portability is gated by rule
  vocabulary against a 179-name `CARCARA_CHECKED_RULES` list
  (`alethe.rs:696-876`) via `Evidence::portable_artifact` (`evidence.rs:878`).
- **External Alethe checking is not exercised by any gate.**
  `tests/carcara_crosscheck.rs` skips-and-passes when the Carcara binary is
  absent, `references/` is gitignored, and `grep -rni carcara scripts/ .github/
  justfile` finds Carcara only in `fetch-references.sh` and in a prose
  classifier. The suite's own head doc says "A skipping suite is a suite that
  has never been shown to fail" (`carcara_crosscheck.rs:29-32`).
- **Reconstruction into kernel terms is WIRED, not test-only** — but
  best-effort. Five production call sites in `evidence.rs` (`:1346`, `:1368`,
  `:2038`, `:3185`, `:3440`, `:4112`), each using `.ok()` so a decline is
  `None`, never an error. Coverage: propositional/CNF, EUF, QF_BV/QF_UFBV,
  LRA/SOS, LIA/Diophantine, quantifiers, datatypes, arrays (private, via the
  fragment dispatcher), NRA, and three string families. **Floating point has
  no reconstruction path at all.**
- **The trust ledger is HAND-MAINTAINED at the enum and DERIVED only in its
  rendering.** `ALL_TRUST_IDS` is a 15-element `const` slice
  (`trust.rs:147-164`) and `is_certified` a hand-written `const match`
  (`trust.rs:322-340`). The golden test (`tests/trust_ledger.rs`) checks that
  the markdown equals the render and that every id has a label — it iterates
  its own list. See [§8](#8-the-trust-ledger).
- **Reachability tally for this area** (within the `full` baseline): 8 of 8
  interpolators WIRED into `solver.rs:305 dispatch_interpolant`, but **all 7
  `*_certified` variants have no caller in `src/`**; the entire
  `bitblast_miter.rs` (1,030 lines) has no caller inside `axeyum-solver`, but IS
  called from outside the crate (`axeyum-bench/src/main.rs:5782`,
  `certificate_process.rs:170`) — **corrected 2026-09-09**, see below;
  `faithfulness.rs` (132 lines) is **test-only**;
  `prove_quant_unsat_alethe` (`quant_alethe.rs`, 1,100 lines) has **no caller
  outside its own test module**; the public `bitblast_step` re-export
  (`lib.rs:321`) is test-only. Full tally in [§10](#10-reachability-tally).
- **`cas-internal` (ADR-0601) exists, but as a Python-derived classification,
  not a Rust type or a schema field.** No enum variant, no
  `artifacts/ontology/fact.schema.json` field. It is computed from a fact's
  `checker_command` by `scripts/validate-facts.py:365-424`. Enforcement is
  asymmetric: an *unclassifiable* checker fails, a *regression* from
  `kernel-reconstructed` fails (ratchet), a **new** `cas-internal` fact is
  unconditionally allowed. See [§7](#7-cas-produced-evidence-and-the-cas-internal-label).
- **`axeyum-machine-evidence` and `axeyum-verify` are downstream consumers, not
  part of solver post-processing.** Both depend on `axeyum-solver` with
  `features = ["full"]`; nothing depends on them; neither imports
  `Evidence`. See [§9](#9-axeyum-machine-evidence-and-axeyum-verify).

---

## 1. The evidence matrix

One row per verdict class / route. `Evidence` variant names are from
`evidence.rs:371-838`; `kind_label` from `:927-1013`; the re-checker from
`recheck_certificate` (`:1097-1375`); `portable` from `portable_artifact`
(`:878-921`), which answers "can a checker outside this process read it?".

Reachability here means: is this variant constructed on a non-test path
reachable from `produce_evidence` (`evidence.rs:3489`) or `produce_qf_bv_evidence`
(`:2078`)?

| Route / theory | Verdict | Evidence artifact | In-tree checker (fn) | Externally portable | Reachability |
|---|---|---|---|---|---|
| default `SatBvBackend` (QF_BV) | `sat` | lifted `Model` | `replay_model` `sat_bv_backend.rs:2424`, unconditional | n/a | WIRED `sat_bv_backend.rs:2387` |
| any route via `produce_evidence` | `sat` | `Evidence::Sat(Model)` | `check_model` `quant_sat_cert.rs:408` via `evidence.rs:1103` | n/a | WIRED |
| QF_BV small / finite Bool-BV | `unsat` | `UnsatTermLevel{cases,bits}` / `UnsatFiniteDomainEnum` | `certify_qf_bv_by_enumeration` / `certify_finite_bv_by_enumeration` `certify.rs:53,74` | no (recomputed, no artifact) | WIRED `evidence.rs:1119,1131,2173,4215` |
| QF_BV Alethe fragment | `unsat` | `UnsatAletheProof(Vec<AletheCommand>)` | `check_alethe` `alethe.rs:937` via `evidence.rs:1142` | Alethe, **iff rule vocabulary ⊆ Carcara** (`evidence.rs:879-886`) | WIRED `evidence.rs:2197` |
| QF_BV general | `unsat` | `Unsat(Some(UnsatProof))` = DIMACS + DRAT + optional LRAT (`proof.rs:49-68`) | `UnsatProof::recheck` `proof.rs:107` → `check_lrat` (accepting authority) ∧ `check_drat_backward`; `check_drat` when no LRAT | DRAT (drat-trim) | WIRED `evidence.rs:2215+` |
| QF_ABV / QF_UFBV / QF_DT | `unsat` | `UnsatAletheProof` from the zero-trust emitters | `check_alethe` | Alethe (vocabulary-gated) | WIRED `evidence.rs:4376,4386,4391,4396` |
| QF_LIA / QF_LRA | `unsat` | `UnsatArithAletheProof` (`lia_generic`/`la_generic`) | `check_alethe_lra` `evidence.rs:1150` | **excluded by construction** (`evidence.rs:908-913`) | WIRED `evidence.rs:4459,4464` |
| QF_UFLIA / QF_UFLRA | `unsat` | `UnsatArithAletheProof` | `check_alethe_lra` | excluded | WIRED `evidence.rs:4423,4428,4433` |
| guarded finite-`Int` ∀ | `unsat` | `UnsatGuardedQuantAletheProof{proof,universal}` | `check_alethe_lra_guarded_inst_against` `evidence.rs:1168` (also re-verifies every `assume` against the original assertions) | Alethe, vocabulary-gated — in practice **no** (`forall_inst_guarded` + `lia_generic`) | WIRED `evidence.rs:4491,4519` |
| QF_LRA conjunctive | `unsat` | `UnsatFarkas(FarkasCertificate)` | `FarkasCertificate::verify` `evidence.rs:1176` | no | WIRED |
| lazy-SMT LRA / arith | `unsat` | `UnsatLraDpll` / `UnsatArithDpll` | `.verify(arena)` `evidence.rs:1177-1178` | `UnsatArithDpll` → DRAT (`evidence.rs:893`) | WIRED |
| NRA SOS | `unsat` | `UnsatSos{certificate, lean_module}` | `SosCertificate::verify` + re-run `reconstruct_sos_to_lean_module` (`evidence.rs:2036`) | no | WIRED `evidence.rs:3185` |
| integer systems | `unsat` | `UnsatDiophantine{equalities,certificate,lean_module}` | `check_diophantine_certificate` + re-run `reconstruct_diophantine_to_lean_module` (`:2054`) | no | WIRED `evidence.rs:3440` |
| bounded int blast | `unsat` | `UnsatBoundedIntBlast(...)` (carries DRAT in `bv_proof`) | certificate recheck; regenerates DIMACS and rechecks DRAT | DRAT (`evidence.rs:893`) | WIRED |
| quantified BV (3 families) | `unsat` | `UnsatBvAlternationCounterexample`, `UnsatBvConjunctiveUniversalInstance`, `UnsatBvPositiveUniversalInstanceSet` | per-variant `check_*` in `quant_bv_*_cert.rs` | DRAT (`evidence.rs:894-896`) | WIRED |
| ~40 further certificate families (arrays, datatypes, EUF, NRA sub-cases, structural, string) | `unsat` | one typed certificate per family | one `check_*` per family, all reached from `recheck_certificate` | no | WIRED |
| strings: word clash | `unsat` | `UnsatWordClash(WordClashCertificate)` | word-clash recheck | Alethe rule `WORD_CLASH_RULE` — axeyum-internal, so no | WIRED `evidence.rs:4098` |
| strings: regex emptiness | `unsat` | `UnsatRegexEmptiness{..., lean_module}` | re-run `reconstruct_regex_emptiness_to_lean_module` (`evidence.rs:1346`) — the kernel gate | no | WIRED |
| strings: length abstraction | `unsat` | `UnsatStringLength{certificate, lean_module}` | `check_string_length_refutation` + re-run reconstruction (`:1362-1369`) | no | WIRED |
| **NRA fallback** | `unsat` | **none** — `Unsat(None)` | none; `check_outcome` → `NothingToCheck(UncertifiedUnsat)` | no | WIRED `evidence.rs:3144` |
| **`solve` general fallback** | `unsat` | **none** — `Unsat(None)` / `Unsat(cert=None)` | none | no | WIRED `evidence.rs:3814,3826` |
| **timeout-budgeted fallback** | `unsat` | **none** (deliberate: keeps the front door timely) | none | no | WIRED `evidence.rs:3814` |
| **string front door fallback** | `unsat` | **none** — `Unsat(None)` | none | no | WIRED `evidence.rs:4119` |
| **difference logic (large)** | `unsat` | **none** — `dl_decided_report` returns a bare `unsat` above the certifying routes' size | none | no | WIRED `evidence.rs:2596`, called `:3525` |
| any route | `unknown` | `Unknown(UnknownReason)` | none by design; `NothingToCheck(Undecided)` | n/a | WIRED |

### The routes with no checkable `unsat` evidence

This is the finding the matrix exists to state plainly. Measured by
`grep -n "Evidence::Unsat(None)" crates/axeyum-solver/src/evidence.rs`
(29 hits, of which **8 are literal constructions on non-test paths** — `:2162`, `:2282`, `:2348`, `:2406`, `:2643`, `:3144`, `:3814`, `:4119` — plus one path at `:3826` that passes a `None` certificate through):

| Site | Route | Why nothing is produced |
|---|---|---|
| `evidence.rs:3144` | NRA (`check_with_nra`) | documented trust gap: "no transferable certificate yet" (`:3806-3809`) |
| `evidence.rs:3814` | any `solve` `unsat` under an explicit timeout | the DRAT export is skipped to keep the front door timely (`:3805-3813`) |
| `evidence.rs:3826` | `solve` `unsat` where `reduction_unsat_certificate` returns `None` | not a literal `Unsat(None)` but the same outcome; `theory_refutation_steps()` records the trust ids instead (`:3818-3825`) |
| `evidence.rs:4119` | string front door | "a correct bare-but-sound `Evidence::Unsat(None)`" (`:4033`) |
| `evidence.rs:2162,2282,2348` | QF_BV export declines (node/CNF budget, check-budget overrun) | `:2247` "the honest bare `Evidence::Unsat(None)`" |
| `evidence.rs:2406` | LRA route with no Farkas certificate | |
| `evidence.rs:2643` | CDCL(T) theory refutation | trust step `SatRefutationModuloTheory`, which is `is_certified() == false` |

None of these is a wrong verdict and none is mislabeled — `kind_label` was
deliberately split so `Unsat(None)` reads `"unsat-uncertified"` rather than
`"unsat-drat"` (`evidence.rs:929-937`, which records the incident where the
collapsed label "advertised a DRAT refutation that does not exist"). But
against the stated identity — *untrusted fast search, trusted small checking* —
these routes deliver only the first half. The honest one-line summary is: the
finite/BV core and the linear-arithmetic core carry checkable `unsat`; **NRA,
the general `solve` fallback, the timed front door, difference logic at scale,
and the string front door do not.**

### `is_certified` vs. `check_outcome`

`Evidence::is_certified` (`evidence.rs:1381`) is a static `matches!` over
variant names; `check_outcome` (`:1062`) is the run that redeems it. The two
are tied together by `tests/certified_implies_revalidatable.rs`, which
re-parses the SMT-LIB text into a **fresh arena** before re-checking
(`:33-38`) — checking against the producer's own arena "would pass for any
certificate". That suite carries a real non-vacuity guard: it fails if fewer
than 3 rows produce certified evidence and fewer than 3 re-validate
(`:356-377`). It is nonetheless an "every X" test over a hand-written
`QUERIES` list (`:49`), so it measures the queries someone remembered to add,
not the 66 variants.

---

## 2. What the default (`qfbv`) build can produce

`crates/axeyum-solver/Cargo.toml:40` — `default = ["qfbv"]`, and
`qfbv = []` (`:44`) pulls in nothing. `axeyum-lean-kernel` is optional
(`Cargo.toml:25`) and enabled only by `full` (`:55`). `mod model;`
(`lib.rs:56`) and `mod proof;` (`lib.rs:67`) are in the **default** module
set; `pub mod proofs` (`lib.rs:305`) is ungated, but every submodule inside it
(`alethe` `:315`, `end_to_end` `:349`, `evidence` `:359`, `faithfulness`
`:375`, `lean` `:381`) is `#[cfg(feature = "full")]`.

| Artifact | default `qfbv` | `full` |
|---|---|---|
| `Model` + unconditional replay | yes (`sat_bv_backend.rs:2387`) | yes |
| `UnsatProof` (DIMACS+DRAT+LRAT) and `UnsatProof::recheck` | yes (`lib.rs:945-951`) | yes |
| `export_qf_bv/abv/aufbv/uf/lia_unsat_proof`, `export_datatype_unsat_proof` | yes (`lib.rs:945-951`) | yes |
| `Evidence` / `EvidenceReport` / `produce_evidence` | **no** (`lib.rs:359`) | yes |
| Alethe emission and `check_alethe` re-validation | **no** (`lib.rs:315`) | yes |
| `certificates::*` (≈70 certificate families) | **no** (`lib.rs:433`) | yes |
| `interpolation::*` | **no** (`lib.rs:862`) | yes |
| kernel reconstruction (`proofs::lean`) | **no** — the kernel crate is not even a dependency | yes |
| `check_model`, `certify_*_by_enumeration`, miter, faithfulness | **no** | yes |
| Z3 oracle + its `replay_sat` | no | `z3` only |

So the *shipped default profile* can produce exactly two evidence artifacts:
a replayed model and a DRAT/LRAT `UnsatProof`. Everything else in this
inventory requires `--features full`.

---

## 3. `sat` model replay: where it actually runs

CLAUDE.md states as a hard rule: "Every `sat` result must be checkable by
evaluating the original term against the lifted model." The code satisfies the
weaker reading (the maps are kept, so a caller *can* check) universally, and
the stronger reading (the solver *does* check) route by route.

| Site | Scope | Always / conditional |
|---|---|---|
| `sat_bv_backend.rs:2387` → `replay_model` `:2424` | default QF_BV backend, both one-shot and warm | **always**, not a debug assertion; a false/non-Bool assertion is `SolverError::Backend`, an unevaluable one degrades to `Unknown` (`:2459-2464`) |
| `sat_bv_backend.rs:417-460` | shared-guard split mirror | always; a non-replaying split model is discarded |
| `preprocess.rs:174-210` | preprocessed models | always on that path |
| `abv.rs:242-256`, `aufbv.rs:112-118` | array / AUFBV | always on those paths |
| `lia.rs:113-120` | int-blast | always |
| `combined.rs:222-229`, `dpll_t.rs:1033-1047` | theory combination, lazy SMT | always |
| `nra.rs:271`, `nia_linearize.rs:1557`, `ufbv_online.rs:3136`, `uflra_online.rs:938`, `array_fifo.rs:206`, `quant_bv_model_sat_search.rs:294` | per-route | always on those paths |
| `strategy.rs:202` → `replay_sat` `:210` | **Z3 oracle strategy only** | `#[cfg(feature = "z3")]` — FEATURE-GATED (not `full`) |
| `evidence.rs:1103` → `check_model` | `Evidence::Sat` re-validation | only when a consumer calls `check`/`check_outcome` |
| `quant_sat_cert.rs:408 check_model` | the documented canonical replay | a **public API for callers**; the solver does not invoke it on every `sat` |

**What I could not determine by reading alone:** whether *every* `sat`-returning
path in the ≈200 `full` modules replays. There is no single choke point to
audit, and no test named "every route replays its model". A grep for
`CheckResult::Sat(` in `crates/axeyum-solver/src` returns hundreds of hits
across dozens of modules; verifying each would need either a build-time
instrumentation of `Model` construction or a derived test. **This is the
concrete gap:** the invariant is stated in CLAUDE.md and enforced by
convention at ~13 sites, not by construction. A `Model` that could only be
built through a replaying constructor, or an "every route that returns
`CheckResult::Sat` replays" test derived from the module list, would close it.
`[unverified]` — a build would be needed to instrument it.

Related: `faithfulness.rs` (132 lines) is the sampled dual for `unsat` — it
compares the bit-blasted AIG against the term evaluator on random assignments
(`check_qf_bv_faithfulness`, `:60`). Its head doc is explicit that "It is
sampling, not a proof" (`:15`). **TEST-ONLY**: `grep -rn
"check_qf_bv_faithfulness" --include=*.rs crates/ examples/` finds only
`tests/faithfulness.rs:7,27,44,59` and a doc-comment mention at
`bitblast_miter.rs:12`.

---

## 4. Alethe emission and checking

### Emitters

| Module | LOC | Fragment / role | Reachability |
|---|---|---|---|
| `qfbv_alethe.rs` | 1861 | QF_BV bitblast→CNF→resolution; `prove_qf_bv_unsat_alethe` (+`_lowered`, `_route2`, `_ext_compare`) | WIRED `evidence.rs:2197`; `_lowered` WIRED from the three reduction emitters |
| `alethe_lra.rs` | 1446 | LIA/LRA `lia_generic`/`la_generic`; `prove_{lia,lra,uflra,uflia_opaque}_unsat_alethe`; also `check_alethe_lra` | WIRED `evidence.rs:4428,4433,4459,4464` |
| `qfdt_simp_alethe.rs` | 1349 | datatype simplification | WIRED `evidence.rs:4396`; the two `*_carcara` helpers TEST-ONLY (`tests/datatype_{distinct,injective}_cert.rs`) |
| `qfufbv_alethe.rs` | 1281 | Ackermann functional consistency | WIRED `evidence.rs:4386` |
| `bitblast_alethe.rs` | 1140 | per-operator `bitblast_*` step builders | `bitblast_op_step`/`bv_term_to_alethe` WIRED (`qfbv_alethe.rs:73`); the **publicly re-exported `bitblast_step` (`lib.rs:321`) is TEST-ONLY** |
| `quant_alethe.rs` | 1100 | e-matching quantifier refutations | **NO CALLER FOUND.** `grep -rn "prove_quant_unsat_alethe" --include=*.rs crates/ examples/ benches/` returns only `lib.rs:337` (re-export) and its own `#[cfg(test)]` module (`:782-1095`) |
| `qfabv_alethe.rs` | 1013 | array read-over-write / select congruence | WIRED `evidence.rs:4376`; `*_row_same`/`*_row_diff_carcara` TEST-ONLY (`tests/carcara_crosscheck.rs:2441,2552`) |
| `euf_alethe.rs` | 943 | QF_UF congruence | WIRED (via `quant_alethe.rs:163` and the zero-trust chain) |
| `qfabv_elim_alethe.rs` | 564 | array elimination | WIRED `evidence.rs:4391` |
| `word_alethe.rs` + `word_alethe/tests.rs` | 490 + 326 | string word-equation clash; rule `WORD_CLASH_RULE` | WIRED `evidence.rs:4098` |
| `skolem_alethe.rs` | 299 | Skolemization certificate | WIRED `reconstruct.rs:2836` |
| `qfuflia_alethe.rs` | 247 | QF_UFLIA congruence + arithmetic | WIRED `evidence.rs:4423` |

Total 11,733 lines of emitters.

### The rule set and the checker

- In-tree checker: `axeyum_cnf::check_alethe` (`alethe.rs:937`) and
  `check_alethe_with` (`:956`), which takes a callback for theory rules so the
  CNF crate stays arithmetic-free. `check_alethe_lra`
  (`axeyum-solver/src/alethe_lra.rs`) plugs in the Farkas re-derivation.
- The checker natively handles ~29 rule names (`and`, `or`, `cong`,
  `eq_congruent`, `eq_reflexive`, `eq_symmetric`, `eq_transitive`, `equiv*`,
  `not_equiv*`, `refl`, `symm`, `trans`, `xor_*`, `arrays_row`,
  `read_over_write`, `read_over_write_same`, plus `resolution`/`th_resolution`).
- Carcara's checkable vocabulary is pinned as a 179-name sorted `const`
  (`alethe.rs:696-876`); `is_carcara_checked_rule` (`:886`) and
  `non_carcara_checked_rules` (`:905`) drive the portability gate.
- Three rules the in-tree checker accepts are **not** in Carcara's list:
  `read_over_write`, `read_over_write_same`, and (from the emitters)
  `bv_poly_simp`. `lia_generic` is also absent — Carcara has no checker for it
  (`alethe.rs:881-884`). So a proof our checker accepts is not automatically
  externally checkable, and `portable_artifact` (`evidence.rs:878`) is the
  place that distinguishes them. Its doc records both a 1.75× undercount and
  an overcount that this gate was written to fix (`:846-875`).

### Is external checking exercised by a gate? No.

- `tests/carcara_crosscheck.rs` shells out to a `carcara` binary
  (`AXEYUM_CARCARA_BIN`, or `references/carcara`), and **skips (printing a
  note, passing) when the binary is absent** (`:10-12`). `references/` is
  gitignored.
- `grep -rni "carcara" --include=*.sh --include=*.py --include=*.yml
  --include=justfile scripts/ .github/ justfile` finds it only in
  `scripts/fetch-references.sh:24` and in `scripts/check-capability-assurance.py`
  (a regex over prose, not a run of Carcara).
- **This is a checker that cannot fail in CI.** The suite's own header says so
  (`:29-32`): "five of them failed the first time one ran". Any claim that
  axeyum's Alethe proofs are Carcara-accepted rests on a manual run, not on a
  gate.
- The one *external* checker that a `just` recipe does run is drat-trim, via
  `just claims` (`justfile:1909-1912`) and `just interpolant-certificate`
  (`justfile:1922-1923`), the latter with `AXEYUM_REQUIRE_DRAT_TRIM=1` so a
  missing binary is a failure rather than a skip. Neither is in
  `scripts/check.sh` or `just check` — `justfile:1905-1908` says so explicitly
  ("Deliberately NOT part of `check`").

---

## 5. Reconstruction into Lean-kernel terms

### Modules

| Module | LOC | Role (from its own head doc) |
|---|---|---|
| `reconstruct.rs` | 4175 | Alethe→Lean over the EUF/equality fragment, plus the **front door**: fragment scan (`scan_proof_fragment` `:1648`), dispatch, module rendering, size cap |
| `reconstruct/arithmetic.rs` | 5511 | kernel-checked LRA and SOS (`reconstruct_lra_proof` `:2784`, `reconstruct_sos_proof` `:2858`) |
| `reconstruct/quant_bv_instance_set_lean.rs` | 3725 | ADR-0134 positive-universal Bool/BV instance sets and 6 sibling quantified-BV families |
| `reconstruct/datatype.rs` | 2311 | **axiom-free** datatype field rules; no `pub fn`, consumed at `reconstruct.rs:125,130` |
| `reconstruct/resolution.rs` | 2421 | propositional resolution and RUP; `resolution.rs:595` documents `add_declaration` as "the per-step kernel gate" |
| `reconstruct/bitblast.rs` | 1954 | bit-blast and QF_BV / QF_UFBV (`:1155`, `:1216`) |
| `reconstruct/direct.rs` | 1608 | ~35-arm structural-certificate dispatcher (`:1509`), called from `reconstruct.rs:2554`; this is where the **array** reconstructors live (`:911`, `:1073`, `:1096`, `:1119`, `:1390`, `:1417`), all private |
| `reconstruct/cnf.rs` | 1576 | Tseitin CNF-introduction (`reconstruct_cnf_intro_rule` `:769`) |
| `reconstruct/quantifier.rs` | 855 | universal instantiation and existential elimination (`:266`, `:658`) |
| `reconstruct/equality.rs` | 533 | Alethe equality rules (`reconstruct_eq_step` `:41`) |
| `reconstruct/arithmetic/*` (9 files) | 6083 | ordered-ring generalization (`ordered_ring.rs`, 1596), monomial bound, signature, string length, zero product, Positivstellensatz, the ADR-0605 `AxReal` call-site guard, and `control.rs` — the deliberate 1-axiom negative control that makes "zero axioms" falsifiable |
| `int_reconstruct.rs` + `int_reconstruct/*` | 3495 + 5481 | Diophantine, integer inequality, affine growth, Euclidean residue, equality partition, counterexample cover |
| `lex_reconstruct.rs` (+ tests) | 392 + 345 | lexicographic `str.<=`/`str.<` over the free-monoid string prelude |
| `word_reconstruct.rs` | 889 | word-equation refutation (ADR-0053); **not** re-exported in `proofs::lean`, only at the crate root |
| `regex_reconstruct.rs` | 696 | regex derivative-emptiness (ADR-0054) |

`reconstruct/` alone is 34,284 lines including its 5,798-line test module.

### Coverage: what can reconstruct, and what cannot

| Theory | Reconstructs? | Evidence |
|---|---|---|
| propositional / CNF / resolution | yes | `reconstruct_resolution_proof`, `reconstruct_cnf_intro_rule` |
| EUF / QF_UF | yes | `reconstruct_qf_uf_proof`, `reconstruct_eq_step` |
| QF_BV, QF_UFBV, bit-blast | yes | `reconstruct_qf_bv_proof`, `reconstruct_qf_ufbv_proof`, `reconstruct_bitblast_step` |
| LRA / Farkas / SOS | yes | `reconstruct_lra_proof`, `reconstruct_sos_proof`, `refutation_over_int_axioms` |
| LIA / integers | yes | 10 exported `reconstruct_int_*` / `reconstruct_diophantine_*` entry points |
| quantifiers (Bool/BV/Int) | yes | 9 exported `reconstruct_*_to_lean_module` |
| datatypes | yes, but **not individually re-exported** | `reconstruct/datatype.rs`, reached via `reconstruct.rs:130` |
| arrays | yes, but **all private** | 6 fns in `reconstruct/direct.rs`, reachable only via `prove_unsat_to_lean_module` |
| NRA (product, monomial bound, zero product, even power) | yes, **not in `proofs::lean`** | `reconstruct.rs:3250,3324,3353`, `direct.rs:885` |
| strings (length, lex, regex, word) | yes | `reconstruct_string_length_to_lean_module`, `reconstruct_lex_clash_to_lean_module`, `reconstruct_regex_emptiness_to_lean_module`; `word_reconstruct` root-only |
| **floating point** | **no** | `grep -niE "float\|floating\|fpa\|RoundingMode" crates/axeyum-solver/src/reconstruct.rs crates/axeyum-solver/src/reconstruct/` → 1 hit, a doc comment in `reconstruct/tests.rs:515`; `ProofFragment` has no FP variant |

### The kernel seam (the kernel crate itself is out of scope)

- Dependency: `crates/axeyum-solver/Cargo.toml:25`
  `axeyum-lean-kernel = { path = "../axeyum-lean-kernel", optional = true }`,
  enabled only by `full` (`:55`).
- **`Kernel::add_declaration` is the trust anchor and is called from 24
  non-test sites**: `reconstruct.rs:463,562,587,2185,3914`;
  `reconstruct/resolution.rs:54,94,615`; `reconstruct/cnf.rs:175`;
  `reconstruct/direct.rs:194,225`; `reconstruct/bitblast.rs:1645`;
  `reconstruct/arithmetic.rs:632,761`;
  `reconstruct/arithmetic/ordered_ring.rs:331,482,518,660,727,1419,1478`;
  `reconstruct/arithmetic/ordered_ring/setoid.rs:479,1113`;
  `int_reconstruct.rs:213,2782,3102`; `lex_reconstruct.rs:211,231`;
  `word_reconstruct.rs:307,327,348`; `regex_reconstruct.rs:288`;
  `reconstruct/datatype.rs:378,682,755,1654,1683,2185`.
- `Kernel::axiom_footprint` — 2 call sites: `reconstruct.rs:2197` (in
  `ctx_refutation_axiom_footprint`, `:2175`) and
  `reconstruct/arithmetic/ordered_ring.rs:1035`.
- `Kernel::environment()` — `reconstruct/resolution.rs:253`,
  `reconstruct/arithmetic/signature.rs:428,623`, and 5 sites in `setoid.rs`.
- **Checking is term-directed, not string-directed.** Reconstruction builds
  `ExprId`s in a live `Kernel`; every `add_declaration` type-checks. The
  rendered Lean module is an output artifact — `evidence.rs:1343` says "the
  stored module string is never trusted on its own". There is no Lean-source
  parser inside `axeyum-solver`; turning a module back into declarations
  happens only in tests via the external `lean` binary
  (`tests/lean_crosscheck.rs:247`, `tests/lean_module_fixtures.rs:124,198`),
  and `lean_crosscheck.rs:304` skips when the binary is absent — the same
  skip-and-pass shape as the Carcara suite.
- `MAX_LEAN_MODULE_BYTES` (`reconstruct.rs:2413`) = 64 MiB. It bounds what is
  *returned*, not the peak allocation; the doc (`:2400-2412`) records
  pathological cases returning `Ok` at 625 MB and 2.38 GB, and the rationale
  "a route that SUCCEEDS at that size is worse than one that declines".
- `STRUCTURAL_ATTESTATION_MARKER` (`reconstruct.rs:1205`) —
  `-- axeyum-lean-module-content: structural-attestation`, stamped on modules
  that assert an opaque proposition and its negation and contain **none** of
  the reasoning. `LeanModuleContent::of_module_source` (`:1210`) classifies by
  reading the artifact, so a table edit alone cannot defeat the decline in
  `prove_unsat_to_lean_theory_module` (`:2458`). This is a good instance of
  the discipline the contributor guide asks for: the guard reads its subject.
- `refutation_axiom_footprint` (`ordered_ring.rs:1468`) declares the proof as
  a fresh probe `Theorem : False` and returns the kernel's own footprint.
  `carrier_axioms_of` (`:1544`) keeps footprint entries **outside**
  `axeyum.reconstruct.`; `minted_axioms_of` (`:1527`) keeps non-query-local
  entries **inside** it — it exists because a route could otherwise "buy a
  zero-carrier-axiom result by minting what it needs under its own name". An
  honest claim needs both empty.

### Reachability

`grep -rn "reconstruct_" crates/axeyum-solver/src/evidence.rs` — 8 hits, 6 on
production paths: `:1346` and `:1368` re-run reconstruction inside
`recheck_certificate` (so the kernel gate runs on the consumer's `check`);
`:2038`, `:2054` do the same for SOS and Diophantine; `:3185`, `:3440`,
`:4112` attach `lean_module` at production time. Every one uses `.ok()`, so a
fragment outside coverage still ships self-checked-but-not-kernel-checked
evidence. **Classification: WIRED under `full`, absent from the default build.**

14 integration suites mention lean/reconstruct/kernel; 13 are
`#![cfg(feature = "full")]`, and `tests/lean_module_fixtures.rs` is
deliberately ungated because it links no solver API — it feeds committed
fixtures to the real `lean` binary.

---

## 6. Interpolation and the miter

### Interpolants

Eight interpolators, all reached from one dispatcher,
`solver.rs:305 dispatch_interpolant`, in order LRA → LRA-CNF → LIA → LIA-CNF →
EUF → UFLRA → UFLIA → BV (`solver.rs:310,316,320,326,329,331,333,335`), itself
reached from `Solver::interpolant` (`:243`) and `interpolant_explained` (`:266`).

| Module | LOC | Fragment | Craig-condition checker | Reachability |
|---|---|---|---|---|
| `interpolant.rs` | 385 | conjunctive QF_LRA (Farkas) | `verify_interpolant` `:320` (vocab `:329`, `A∧¬I` `:349`, `I∧B` `:357`) | WIRED `solver.rs:310`, `imc_lra.rs:340`, `lia_interpolant.rs:116`, `uflra_interpolant.rs:120` |
| `lra_interpolant_cnf.rs` | 723 | disjunctive QF_LRA (McMillan, DPLL(T) lemmas) | `verify_interpolant` `:193` | WIRED `solver.rs:316` |
| `lia_interpolant.rs` | 801 | conjunctive QF_LIA (relax → interpolate → integer recheck) | `verify_interpolant` `:351` on the **original integer** partitions | WIRED `solver.rs:320` |
| `lia_interpolant_cnf.rs` | 622 | disjunctive QF_LIA | `verify_interpolant` `:158` | WIRED `solver.rs:326` |
| `euf_interpolant.rs` | 773 | ground QF_UF | `verify_interpolant` `:585` (vocab over symbols **and** function ids) | WIRED `solver.rs:329` |
| `uflra_interpolant.rs` | 505 | QF_UFLRA (Ackermannize → LRA) | `verify_uflra_interpolant` `:168`, `pub` but **not re-exported** | WIRED `solver.rs:331` |
| `uflia_interpolant.rs` | 581 | QF_UFLIA | `verify_uflia_interpolant` `:174`, `pub` but not re-exported | WIRED `solver.rs:333` |
| `bv_interpolant.rs` | 667 | QF_BV (joint bit-blast → propositional interpolant → lift) | `verify_interpolant` `:564`, **plus** the propositional layer's own DRAT-backed check | WIRED `solver.rs:335`, `imc.rs:280` |
| `axeyum-cnf/src/interpolant.rs` | 694 | propositional (McMillan 2003, off the LRAT proof) | `verify_interpolant` `:621`; conditions 1 and 2 Tseitin-encoded and discharged with `solve_with_drat_proof` + DRAT recheck (`:685,692`) | WIRED from `bv_interpolant.rs:173`, `lra_interpolant_cnf.rs:156` |

**The guarantee.** Uniform verify-before-return: nine independent
`verify_interpolant`-style functions, each checking vocabulary containment and
both Craig unsat conditions **with a decider different from the construction
path**, each declining to `None` on any doubt. No interpolator returns an
unverified result. That is a strong property and it is implemented, not just
documented.

**Independently checked?** Yes in-tree, at the point of production. The only
route to an *outside* check is `just interpolant-certificate`
(`justfile:1922-1923`), which runs
`cargo test -p axeyum-cnf --test propositional_interpolant_certified` with
`AXEYUM_REQUIRE_DRAT_TRIM=1` so a missing binary fails rather than skips —
and that recipe is not in `check.sh` or `just check`.

**Dead surface:** all seven `*_certified` variants (`lra_interpolant_certified`,
`qf_bv_interpolant_certified`, `qf_uf_interpolant_certified`,
`lia_interpolant_certified`, `uflia_interpolant_certified`,
`uflra_interpolant_certified`, `propositional_interpolant_certified`) have
**no caller in `crates/axeyum-solver/src`** — only `lib.rs` re-exports and
`tests/`.

> **Two corrections, 2026-09-09.** (1) The original text continued
> "`uflia_interpolant_certified` has no caller anywhere, including `tests/`."
> That was FALSE when written: it has 12 callers in `tests/` — 7 in
> `tests/uflia_interpolant.rs` and 5 in `tests/lean_crosscheck.rs`. Same
> correction applies to the `NO CALLER FOUND` row below. (2) The finding itself
> is now RESOLVED for six of the seven: roadmap item 2.8 wired them, so
> `dispatch_interpolant` consumes `qf_bv`, `qf_uf`, `lra`, `lia`, `uflra` and
> `uflia` certified variants. `propositional_interpolant_certified` remains
> deliberately unwired — its DRAT lives in the CNF encoding's variable space and
> would not cover the lift back to terms. Note only FOUR of the six are
> reachable through the shipping ladder: `certify_qf_bv` is shadowed by the
> ground-EUF rung and `certify_uflia` is unreached (roadmap 2.8b).

### Miter and end-to-end certification

`bitblast_miter.rs` (1,030 lines) builds one AIG holding both the production
`axeyum-bv` encoding and a separately coded reference bit-blaster over shared
inputs, forms the miter `OR(fast_bit XOR ref_bit)`, and refutes it with the
proof-producing SAT core (head doc `:6-9`). It **checks** the disagreement
space over all inputs by DRAT (a failed proof check escalates to
`SolverError::Backend`, `:160-162`) and **trusts** the reference bit-blaster
and Tseitin equisatisfiability (`:19-21`).
`certify_qf_bv_unsat_end_to_end` (`:246`) composes miter + CNF DRAT to close
the term↔CNF gap; `EndToEndUnsatOutcome::recheck` (`:209`) re-derives both
DRAT proofs from text alone.

**Reachability: NO PRODUCTION CALLER.**
`grep -rn "certify_bitblast_by_miter\|certify_qf_bv_unsat_end_to_end"
crates/axeyum-solver/src` returns only `lib.rs:352,353,1027,1028`
(re-exports), the functions' own definitions and self-delegation, and the
in-file `#[cfg(test)]` module (`:785,803,823,839,862`). The one external
**Correction (2026-09-09, coordinator).** The claim above that the miter has no
production caller is WRONG, and the error was a search that looked for the
module name. Its exported entry point is
`certify_qf_bv_unsat_end_to_end_within`, whose name does not contain "miter",
and it is called from `axeyum-bench/src/main.rs:5782`,
`axeyum-bench/src/certificate_process.rs:170` (both in the shipped bench binary,
not tests) and `axeyum-verify/tests/tock_log2_external.rs:211`. So the module is
reachable — from the benchmark harness, not from the solve path. The narrower
observation that survives is that nothing in `axeyum-solver` itself calls it, so
a `Solver` user gets no miter check unless they go through the bench crate.

caller is `tests/bitblast_miter.rs:32`. This matters because the trust ledger
lists `TrustId::BitBlast` as **certified** (`trust.rs:324,331`) and the ledger
doc names "the bit-blast miter" as one of the certifying mechanisms
(`trust.rs:8`) — but the miter is not on any shipped path. The bit-blast
reduction is certified in production only when the **Alethe** route fires
(`evidence.rs:2205-2212`), which re-derives every `bitblast_*` step.

`certify.rs` (387 lines, `CertifyOutcome::{CertifiedUnsat, Satisfiable,
DomainTooLarge}` at `:27-37`) is by contrast fully WIRED:
`certify_qf_bv_by_enumeration` at `evidence.rs:1119,2173`,
`reconstruct/direct.rs:644`, `reconstruct.rs:1614`;
`certify_finite_bv_by_enumeration` at `evidence.rs:1131,4215`,
`reconstruct/direct.rs:610`, `reconstruct.rs:1621`.

---

## 7. CAS-produced evidence and the `cas-internal` label

`cas_poly.rs` (1,525 lines) is the untrusted discovery half (normalizes via
`axeyum-cas`'s `MvPoly`); `cas_certificate.rs` (976 lines) is the trusted
re-checker half and **imports nothing from `axeyum-cas`**
(`cas_certificate.rs:1-46`, `cas_poly.rs:1-31`).

| Producer | Checker | Enforcement |
|---|---|---|
| `cas_identity_refutation` `cas_poly.rs:407` | `check_cas_identity_certificate` `cas_certificate.rs:328` | called at `cas_poly.rs:451` **before** returning `Refuted`; failure → `CasOutcome::VerifierRejected` |
| `cas_int_units_refutation` `:481` | `check_cas_int_units_certificate` `:368` | `cas_poly.rs:525` |
| `cas_ideal_refutation` `:605` | `check_cas_ideal_certificate` `:523` | `cas_poly.rs:1054` |

**Reachability: WIRED.** `auto.rs:5119 dispatch_cas_refuters` (calls at
`:5130`, `:5155`) and `auto.rs:5199 dispatch_cas_ideal` (`:5204`), dispatched
from `auto.rs:1694`, `:4659`, `:4674`, `:5418`. Route-trace names
`cas-identity-refuter`, `cas-int-units`, `cas-ideal-refuter`; declines funnel
through `record_cas_decline` (`auto.rs:5243`). Re-exported `#[doc(hidden)]` at
`lib.rs:1063-1072`.

### The `cas-internal` label

ADR-0601 §2 (`docs/research/09-decisions/adr-0601-three-producers-one-trust-anchor.md:42-49`):

> 2. **CAS certificates reconstruct or say so.** The `cas-certificate` route
> splits observably: evidence that reconstructs through the kernel … versus
> evidence that terminates in the CAS's own normal form. The validator must
> distinguish these; a fact of the second kind is honest but is not `checked`
> in the sense the headline uses, and the ledger must not let the two read
> identically.

**The mechanism exists, but not where one would look for it.**

- **No Rust enum variant or constant.** `grep -rni "cas.internal"` over the
  repo (~460 hits, ~130 files) finds the string in Rust only as doc comments,
  and only in `axeyum-cas` and `axeyum-lean-kernel` (e.g.
  `crates/axeyum-cas/src/rationality.rs:59`,
  `crates/axeyum-cas/src/ntheory_certify.rs:27`). Never in `axeyum-solver`.
- **Not a schema field.** `artifacts/ontology/fact.schema.json:89` lists
  `proof_route` as `["kernel-lean", "imported-kernel-lean",
  "kernel-lean-over-import", "smt-term-level", "smt-clausal",
  "search-certificate", "cas-certificate", "none"]` — `cas-internal` is not in
  it and appears nowhere in the schema. Where it appears in facts it is prose
  in `notes`, or an ad-hoc evidence `id` slug (13 files, e.g.
  `artifacts/facts/F-cas-ivt-cbrt2-in-1-2.json:27`).
- **It is derived, in Python, from the `checker_command`.**
  `scripts/validate-facts.py:365 classify_cas_certificate_checker` scans the
  executed `cargo test`/`cargo run` segments: naming `axeyum-lean-kernel` →
  `kernel-reconstructed`; naming only `axeyum-cas` → `cas-internal` (`:402`);
  neither → `unrecognized` (`:404`). `classify_cas_certificate_fact` (`:406`)
  aggregates. 69 facts currently carry `"proof_route": "cas-certificate"`.

**Enforcement is asymmetric, and the asymmetry is deliberate and documented.**

| Condition | Gate | Changes exit status? |
|---|---|---|
| a `cas-certificate` fact whose checker classifies `unrecognized` | `validate-facts.py:524-539` → `fail()` → nonzero exit | **yes** |
| a fact recorded `kernel-reconstructed` that now classifies otherwise | `scripts/check-cas-internal-residue.py:129-148`, ratchet file `scripts/check-cas-internal-residue.ratchet` (16 `kernel-reconstructed` + 45 `cas-internal` rows), `return 1` at `:258`; run at `check.sh:424` and `justfile:393` | **yes** |
| a fact ratcheted by `check-cas-substance.py` downgraded to `cas-internal` | `check-cas-substance.py:235` rule R1, `return 1` at `:439/448/456/463`; `justfile:386-387` | **yes** |
| **a NEW `cas-internal` fact** | none | **no — convention only** |

The last row is stated in the scripts themselves:
`check-cas-internal-residue.py:11` "nothing FAILS if the `cas-internal` share
grows"; `justfile:391-392` and `check.sh:422-423` "a fact regressing to
cas-internal (or vanishing) is refused, a new cas-internal fact is not".
A mutation control exists (`scripts/tests/mutation_controls.py:7263-7278`,
suite `cas-internal-residue`, guard G3), so the ratchet has been shown to be
able to fail.

**Verdict for question 5:** the labeling obligation is met *observably* (the
two classes do not read identically in the ledger) and is *enforced* against
regression, but the label is a derived Python string rather than a typed field,
and growth of the `cas-internal` population is unconstrained by design.

---

## 8. The trust ledger

`trust.rs` (560 lines). `TrustId` (`:26-143`) has 15 variants;
`ALL_TRUST_IDS` (`:147-164`) is the canonical iteration order — a `const`
slice, source order, never hash order.

| Certified (`is_certified() == true`, `trust.rs:324-331`) | Trust hole (`false`, `:332-338`) |
|---|---|
| `BitBlast`, `Tseitin`, `SatRefutation`, `TermLevelEnum`, `Farkas`, `LraDpll`, `Sos`, `Diophantine` | `SatRefutationModuloTheory`, `ArrayElim`, `Ackermann`, `IntBlast`, `DatatypeElim`, `Fpa2Bv`, `XorGaussian` |

8 certified, 7 trust holes — matching the generated ledger's header line
("Trusted base: **7** reduction(s) remain trust holes",
`docs/research/08-planning/trust-ledger.md:10`).

`EvidenceReport.trusted_steps` (`evidence.rs:247`) makes the ledger
per-result: `trust_steps` (`:253`) iterates `ALL_TRUST_IDS` so ordering never
leaks a hash map, and each `TrustStep` records whether *this run* certified
that reduction.

### Derived or hand-maintained?

**Hand-maintained at the enum; derived only in its rendering.** Precisely:

- The *set* of 15 reductions is a hand-written `const` (`trust.rs:147`).
  Nothing enumerates the reductions the code actually performs and compares.
- `is_certified` is a hand-written `const match` (`:322`). If a route lost its
  checker, the `true` would stay `true`; nothing derives it from the presence
  of a checker.
- `docs/research/08-planning/trust-ledger.md` **is** derived:
  `trust_ledger_markdown()` (`:388`) renders it and
  `tests/trust_ledger.rs:14 trust_ledger_doc_is_in_sync` asserts byte equality
  (regenerate with `UPDATE_TRUST_LEDGER=1`). That test is real and would fail
  on drift.
- `tests/trust_ledger.rs:31 trust_ids_are_well_formed` is an "every X" test
  **that iterates its own list**: `for &id in ALL_TRUST_IDS` checking that
  each has a label, a meaning, a pedantic level ≤ 10 and an `ADR-` reference.
  It cannot see a reduction missing from the list, and its name does not say
  so. This is exactly the shape
  `docs/contributor-guide/evidence-and-checker-discipline.md:48-84` warns
  about.
- The related capability table (`capabilities.rs`, 106 `Capability` entries,
  105 with `checked_by`) is likewise hand-maintained.
  `scripts/check-capability-assurance.py` gates it and **does** return 1 on a
  finding (`:322`): it fails if any row omits `checked_by`, if the parser
  matches fewer than 90 entries, or if the `ExternalChecker` count falls below
  `EXTERNAL_FLOOR = 39`. It also cross-checks each `ExternalChecker` row
  against a regex over its own prose `evidence` field (`overstated`, `:184`).
  That is a genuine, falsifiable gate — but its subject is two hand-written
  fields in one Rust file, never the emitting code, so it cannot detect a
  route that stopped producing the artifact it claims.

**Answer to question 7:** the trust ledger tracks reduction steps with a
pedantic level, a certified/hole bit and an ADR reference; the levels are
`BitBlast` 8, `Tseitin` 9, `SatRefutation` 9, `TermLevelEnum` 10, `Farkas` 10,
`Sos` 10, `Diophantine` 10 down to `IntBlast` 3 and `XorGaussian` 3. It is
**hand-maintained**, with a derived rendering and a golden test that protects
the rendering only.

---

## 9. `axeyum-machine-evidence` and `axeyum-verify`

| Crate | src LOC | `#[test]` | Depends on `axeyum-solver`? | Anything depends on it? |
|---|---|---|---|---|
| `axeyum-machine-evidence` | 6,559 (+757 tests) | 21 | yes, `default-features = false, features = ["full"]` | no crate — listed in `[workspace.dependencies]` (`Cargo.toml:53`) but consumed by no member |
| `axeyum-verify` | 20,744 (+19,758 tests) | 366 | yes, same pin | no crate; referenced only as a test target (`justfile:683,1519`) |
| `axeyum-verify-macros` | 2,555 | 9 | no axeyum deps at all | `axeyum-verify` (`crates/axeyum-verify/Cargo.toml:19`) |

- **`axeyum-machine-evidence`** is content-bound evidence for *machine/ISA
  semantics* (`src/lib.rs:1-5`): for each claim (A0 equivalence, A0
  minimality, cross-ISA absolute value, RV64/x64 encodings, symbolic
  two's-complement addition, symbolic memory, three-machine XOR) it emits a
  `*Report` pinning a SHA-256 digest of the semantic source and its finite
  domain, plus a paired `check_*` that recomputes rather than trusting, plus a
  deliberate negative control (`check_*_control`). It touches the solver only
  for BV proof export (`src/symbolic_addition.rs:9`, `src/symbolic_memory.rs:10`:
  `UnsatProof`, `UnsatProofOutcome`, `export_qf_bv_unsat_proof`).
- **`axeyum-verify`** is a bounded Rust verifier: `#[axeyum::verify]` lowers an
  annotated function to `axeyum-ir` with each panic class as an explicit bad
  state, then calls `prove(¬OR(bad_states))` (`src/verify.rs:5,11`). Its
  soundness floor is execution — every counterexample is replayed by running
  the original Rust function (`src/lib.rs:58-65`).
- **Relationship to `evidence.rs`: none.** `grep -rn "Evidence"
  crates/axeyum-verify/src crates/axeyum-machine-evidence/src` returns no
  hits. The dependency edge points downstream only, so `evidence.rs` cannot
  call into them. They are **separate, parallel** evidence systems that
  consume the solver's public `prove`/proof-export API and reimplement
  replay-checking in their own domains. Neither is on the solver's
  post-processing path.

---

## 10. Reachability tally

Within the `full` baseline, for the components this lane inventoried:

| Class | Count | Members |
|---|---|---|
| WIRED | 41 | `replay_model`; `check_model` (from `evidence.rs:1103`); `certify_qf_bv_by_enumeration`; `certify_finite_bv_by_enumeration`; `UnsatProof::recheck`; `check_alethe`/`check_alethe_with`/`check_alethe_lra`; 10 of 12 Alethe emitter modules; 8 interpolators + the propositional one; `minimize_model*` (4 fns, `solver.rs:415,430`); ~66 `Evidence` variants' `recheck_certificate` arms; 6 reconstruction call sites in `evidence.rs`; 3 CAS producers + 3 CAS checkers |
| TEST-ONLY | 8 | `faithfulness.rs::check_qf_bv_faithfulness`; the whole of `bitblast_miter.rs` (4 public fns + `recheck`); `bitblast_step` (the `lib.rs:321` re-export); `prove_qf_abv_row_same/row_diff_alethe_carcara`; `prove_qf_dt_distinct/injective_alethe_carcara` |
| NO CALLER FOUND | 8 | `prove_quant_unsat_alethe` (`quant_alethe.rs`, 1,100 lines — grep: `grep -rn "prove_quant_unsat_alethe" --include=*.rs crates/ examples/ benches/`, only `lib.rs` re-export + its own `#[cfg(test)]`); the 7 `*_certified` interpolant variants (grep: `grep -rn "<name>" crates/axeyum-solver/src` → `lib.rs` re-exports only; `uflia_interpolant_certified` not even in `tests/`) |
| FEATURE-GATED (not `full`) | 1 | `strategy.rs::replay_sat` + `solve_with_oracle`, `#[cfg(feature = "z3")]` (`strategy.rs:192,209`) |

---

## Data flow

The `full`-profile path, in call order:

1. `produce_evidence(arena, assertions, config)` (`evidence.rs:3489`) builds a
   `Provenance` (`SEMANTICS_VERSION`, `LayerVersions::CURRENT`, backend name,
   budgets).
2. Two pre-route hooks: `dl_conjunctive_farkas_report` (called `:3518`, defined
   `:2553`) and `dl_decided_report` (called `:3525`, defined `:2596`).
3. `evidence_route` (`:4871`) classifies by sorts/operators into
   `QfBv | PureReal | Other` (`:4860-4867`).
4. `QfBv` → `produce_qf_bv_evidence` (`:2078`): try term-level enumeration
   (`certify.rs:53`), then the Alethe driver
   (`qfbv_alethe::prove_qf_bv_unsat_alethe`, re-validated by `check_alethe`
   before being emitted, `:2203`), then `drat_qf_bv_evidence`
   (`proof::export_qf_bv_unsat_proof`).
5. `PureReal` → structural pre-solve, SOS, even-power, zero-product, monomial
   bound, Handelman, then the linear Farkas / DPLL(T) route, then NRA
   (`:3125`, bare `unsat`).
6. `Other` → `zero_trust_alethe_certificate` (`:3714`), then
   `uflia_alethe_certificate`, then `reduction_unsat_certificate`
   (DRAT export), then bare `unsat`.
7. Any `Evidence::Sat` carries a `Model` produced by the backend's own
   `replay_model`; `Evidence::UnsatSos` / `UnsatDiophantine` /
   `UnsatStringLength` additionally carry a rendered Lean module from
   `reconstruct*`.
8. A consumer calls `EvidenceReport.evidence.check_outcome(arena, assertions)`
   (`:1062`) → the `NothingToCheck` guards (`:1070-1084`) →
   `recheck_certificate` (`:1097`) → the per-variant checker.
9. `EvidenceReport.trusted_steps` (`:247`) names which reductions this result
   went through and whether this run certified each.

## Entry points and public API

- Default profile: `Model`, `SatBvBackend`, `UnsatProof` + `recheck`, the
  seven `export_*_unsat_proof` functions (`lib.rs:943-951`).
- `proofs::alethe` (`lib.rs:315-347`) — 24 emitter functions plus
  `SkolemCert`, `WordClashCertificate`, `WORD_CLASH_RULE`.
- `proofs::end_to_end` (`:349-356`) — the miter API.
- `proofs::evidence` (`:359-373`) — `Evidence`, `EvidenceCheck`,
  `EvidenceReport`, `NoCheckReason`, `Provenance`, `SEMANTICS_VERSION`, and
  the 18 `produce_*` / `prove*` entry points.
- `proofs::faithfulness` (`:375-379`), `proofs::lean` (`:381-423`).
- `certificates::{arrays, arithmetic, finite_domains, quantifiers,
  structural, uninterpreted_functions}` (`:433-654`).
- `interpolation::{bitvectors, uninterpreted_functions, linear_integer,
  linear_real, uflia, uflra}` (`:862-910`).
- `trust::{ALL_TRUST_IDS, TrustId, TrustStep, trust_ledger_markdown}`
  (`:1502`); also surfaced to Python at `crates/axeyum-py/src/solver/core.rs:855`.

## Tests and gates

- 302 integration suites in `crates/axeyum-solver/tests/`; **297 carry
  `#![cfg(feature = "full")]`** and 28 carry `#![cfg(feature = "z3")]`. All of
  them compile to zero tests and exit 0 without the flag — the trap CLAUDE.md
  documents. Confirm a nonzero test count.
- Post-processing suites specifically: `evidence*.rs` (18 files),
  `*_interpolant*.rs` (8), `*alethe*` / `*proof*` / `*cert*` (≈20),
  `*lean*`/`*reconstruct*` (14), `trust_ledger.rs`, `certify.rs`,
  `bitblast_miter.rs`, `faithfulness.rs`,
  `certified_implies_revalidatable.rs`, `decision_and_evidence_routes_agree.rs`.
- **Two suites skip-and-pass when an external binary is missing:**
  `carcara_crosscheck.rs` (`:10-12`) and `lean_crosscheck.rs` (`:304`). Both
  are the only in-repo evidence that a third party accepts our artifacts.
  `just interpolant-certificate` is the counter-example done right —
  `AXEYUM_REQUIRE_DRAT_TRIM=1` makes a missing binary a failure
  (`justfile:1918-1923`).
- Python gates touching this area: `scripts/check-capability-assurance.py`
  (`check.sh:872`, `justfile:579`), `scripts/check-cas-internal-residue.py`
  + its unittest (`check.sh:424-425`, `justfile:393,404`),
  `scripts/check-cas-substance.py` (`justfile:386-387`),
  `scripts/validate-facts.py`. All return nonzero on a finding.
- `just claims` and `just interpolant-certificate` are the drat-trim gates and
  are **deliberately outside** `just check` (`justfile:1905-1908`).

## Doc drift

### `docs/internals/proof-stack.md` (80 lines) — two stale statements, both about LRAT

1. **Line 40-42:** "a supported RUP-only DRAT proof can be elaborated to the
   current positive-hint LRAT slice for a more explicit propositional check;
   **RAT additions are rejected**."
   **Line 67-68:** "`axeyum-cnf` provides DRAT, **a RUP-only positive-hint
   LRAT checker and elaborator**, and a selected Alethe core."

   Contradicted by `crates/axeyum-cnf/src/lrat.rs:11-20`: "`check_lrat` and
   `elaborate_drat_to_lrat` (and its bounded/progress counterpart) support
   both RUP additions (`LratStep::Add`, positive hints) **and RAT additions**
   (`LratStep::AddRat`, a pivot literal plus one resolution-candidate hint
   block per active clause containing its negation — … ADR-1722). The
   *backward*, core-first elaborator … still declines a RAT core lemma …"
   `LratStep::AddRat` is defined at `lrat.rs:49-70`. The doc's blanket "RAT
   additions are rejected" is now true only of
   `elaborate_drat_to_lrat_backward`, not of the checker or the forward
   elaborator. Both lines should name the engine.

2. **Line 47-51:** "[`axeyum-solver` evidence] packages the verdict,
   artifacts, replay/check results, and deterministic diagnostics. **Stable
   trust IDs identify assumptions and checker steps** so generated artifacts
   can be audited against the [trust ledger](../reference/trust-ledger.md)."
   Accurate in substance (`EvidenceReport.trusted_steps`, `evidence.rs:247`),
   but the link target `docs/reference/trust-ledger.md` is a pointer page; the
   authority is `docs/research/08-planning/trust-ledger.md` (which the pointer
   page itself says, `docs/reference/trust-ledger.md:3-5`). Minor, but a
   reader following the link from `proof-stack.md` lands one hop short of the
   generated table.

3. **No drift** in the rest: the two-obligation framing (lines 7-20), the
   "Not every current backend produces such an artifact… must not be described
   as certificate-checked" caveat (lines 18-20), and the seven-row
   "distinction matters" table (lines 52-62) all match the source. The claim
   at line 74-76 that "unsupported proof constructs must fail closed or remain
   `unknown`" matches `AletheError::UnsupportedRule` (`alethe.rs:150-176`) and
   `ReconstructError` declines.

### `docs/reference/trust-ledger.md` (32 lines) — one stale command, no substantive drift

- **Line 10:** `cargo test -p axeyum-solver --test trust_ledger --features full`.
  Correct and complete: `tests/trust_ledger.rs:4` is
  `#![cfg(feature = "full")]`, so the `--features full` is load-bearing and is
  present. No drift.
- Lines 3-5 correctly redirect to the generated ledger. Lines 14-24 define
  Checked / Validated / Trusted / Absent-partial — these are the
  **`capabilities.rs` `Assurance`** vocabulary (`capabilities.rs:26-40`), not
  the `TrustId` vocabulary the generated ledger uses (`certified` /
  `trust hole`). The page mixes two vocabularies without saying they are
  different taxonomies over different subjects (per-capability vs.
  per-reduction). Not false, but the page is titled "Trust Ledger" and three
  of its four defined terms do not appear in the trust ledger.
- Lines 26-29 ("A checked DRAT proof of a CNF refutation does not automatically
  check the source-to-CNF transform") are exactly right and match
  `trust.rs:8-11`.

I found no other drift in either file; I did not manufacture findings.

## Gaps and open questions

1. **No derived test that every `sat`-returning route replays its model.** The
   invariant is CLAUDE.md's hard rule; enforcement is ~13 hand-written sites.
   What would determine it: a test that enumerates every function returning
   `CheckResult::Sat` (or a `Model` constructor that cannot be reached without
   a replay), in the shape
   `evidence-and-checker-discipline.md:48-84` prescribes — derive the "every X"
   from the authority, not a literal.
2. **No derived test that every `Evidence` variant is exercised by
   `certified_implies_revalidatable.rs`.** Its `QUERIES` list is hand-written
   (`:49`) and its non-vacuity floor is 3 of N rows. 66 variants exist. A
   `match self { … }` exhaustiveness helper (like `kind_label`) that yields a
   fixture per variant would close it.
3. **`TrustId::BitBlast` is marked certified while the miter that certifies it
   has no production caller.** The Alethe route does certify bit-blast
   (`evidence.rs:2205-2212`), so the bit is defensible for queries in that
   fragment — but `is_certified` is per-id, not per-query, and the ledger's own
   prose names the miter (`trust.rs:8`). Determining whether the claim is
   sound for the DRAT route would need the per-result `trusted_steps` measured
   over a corpus. `[unverified]` — needs a run.
4. **Carcara acceptance is unverified in CI.** Nothing in `scripts/`,
   `.github/` or the `justfile` runs Carcara. Every "Carcara-checked" claim in
   `capabilities.rs` rests on a manual run recorded in prose, which
   `check-capability-assurance.py` then classifies by regex. The cheap fix is
   the shape `just interpolant-certificate` already uses: an
   `AXEYUM_REQUIRE_CARCARA=1` mode plus one recipe.
5. **`quant_alethe.rs` (1,100 lines) has no caller.** I could not determine
   whether it was superseded by `quant_finite_cert`'s guarded-instantiation
   route (which *is* wired at `evidence.rs:4491,4519`) or whether the wiring
   was lost. `git log --follow` on the file would answer it.
6. **The `cas-internal` classification is not machine-readable in the fact
   schema.** `validate-facts.py:365-424` re-derives it from a command string
   every run. Adding it to `fact.schema.json` as a stored, validated field
   would let a checker fail on a mislabeled fact rather than on an
   unclassifiable command.
7. **I did not verify any of this by building.** Every reachability claim is a
   grep over source at `ea8515407`; a `cargo build --features full` with
   `-W dead_code` would independently confirm the NO-CALLER-FOUND rows (all
   are `pub` and re-exported, so dead-code analysis will not flag them — a
   call-graph tool would be needed instead).
