# Lane: agent-real-migration — retiring the axiomatized `Real` package

<!-- plan-section: lane-status -->

**The reconstruction context's carrier is now a parameter, and the constructed
reals already satisfy it (`WIP`, agent-real-migration, 2026-08-18).**
`LraReconstructCtx` no longer holds an `ArithPrelude`; it holds a
`RingSignature` — the same 31 field names, so all 158 field reads across
`arithmetic.rs`, `ordered_ring.rs` and `setoid.rs` are unchanged — plus a
`RingEquality` saying *which relation plays the role of equality*. `new()` keeps
its contract and supplies the `Real` package's instance; `try_new()` is the same
without the panic; `with_ring_signature(kernel, sig)` is the seam: a caller
brings its own kernel and names its own carrier.

**The signature is checked, not trusted.** `RingSignature::validate_in` runs five
guards — presence of all 30; the carrier is a `Sort` and its level is *measured*;
the seven operation/relation shapes by `def_eq` against types built from the
signature's own carrier; every law inhabits `Prop`; every `Const` in a law
statement is one of the eight symbols, a propositional connective, or the
signature's declared equality. Each guard is its own function with its own
negative test. **Mutation-verified twice** (before and after the split into
per-guard functions): deleting guard 2, 3, 4 or 5 kills **exactly one** test out
of 1191 and no other; deleting guard 1 kills two, which are its two entry points
(`validate_in` directly, and through `with_ring_signature`) rather than one
shared rejection path.

**Nothing changed today, and that is measured rather than argued.**
`cargo run -q -p axeyum-solver --features full --example ordered_ring_refutation
-- --require-empty` is **byte-identical to the pre-change baseline** (`diff`, all
five fixtures: footprint 0, 39 setoid binders, 30 of 30 non-slot binder types,
0 residual kernel-`Eq` constants). `farkas_over_the_integers` 9/9,
`sos_lean_reconstruct` 14/14, `--lib --features full` 1191/1191, clippy
`-D warnings` clean, `RUSTDOCFLAGS="-D warnings" cargo doc` clean (that gate
caught three broken intra-doc links nothing else did).

**The finding: `CReal` passes the signature check today, unmodified.** A
`RingSignature` built entirely out of `CRealPrelude` — no `Real` package in the
kernel at all — passes all five guards with `equality: Defined(CReal.Equiv)`.
Measured, and committed as a test:

- carrier level **1**, the same `Sort 1` the reconstruction hard-wires its
  `Eq`/`Eq.refl`/`Eq.rec` universe argument at (7 sites). That hard-wiring is
  therefore *not* an obstacle for this carrier — it would be for any other level,
  and `RingSignatureReport::carrier_level` is what would say so.
- exactly **nine** laws stated with `CReal.Equiv` — the same nine the `Real`
  package states with `Eq Real`, so the 39-binder setoid telescope is the right
  shape.
- the same signature claiming `RingEquality::KernelEq` is **refused**, naming
  `CReal.Equiv` as the foreign constant. The positive result is discriminating,
  not vacuous.

**Next slice (B): adopt an equality slot instead of declaring one.** All 18
`SetoidEq` members already exist on `CRealPrelude` — `equiv`, `equiv_refl`,
`equiv_symm`, `equiv_trans`, `add_congr`, `mul_congr`, `neg_congr`, `le_congr`,
`lt_congr`, and the nine `Equiv`-stated laws are `CReal`'s own `add_comm` …
`left_distrib` (the *same* `NameId`s the signature's law slots hold, so the
39-entry telescope stays 39 with no duplicate). So slice B declares **zero new
axioms**. What it needs is a `LraReconstructCtx::adopt_setoid_equality(SetoidEq)`
beside today's `enable_setoid_equality`, which can only *derive* a slot by
declaring nine axioms and rewriting `Eq Real` out of the nine `Real` laws — and
which hard-errors when that rewrite does not fire, so it is a deeper `Real`
dependency, not an escape. Sizing and the rest of the ladder are below.

## The costed plan, with counts

Every count below was re-measured on 2026-08-18. **Six of the eight figures in
the brief this lane was given are wrong**; the corrected ones are in the last
column and the plan is costed against those, not against the brief.

| # | Slice | Surface, measured | Size | Blocked on |
|---|---|---|---|---|
| **A** | *(landed)* carrier is a parameter | 4 files, +1 module, +11 tests | done | — |
| **B** | Adopt a `SetoidEq` from `CRealPrelude` instead of declaring one | 18 slot members, **all already exist**; 0 new axioms; 1 new ctx method + a shape guard mirroring `declare_setoid_equality`'s 18 constructions | M (~300 lines + tests) | A |
| **C** | Reconstruct + generalize a Farkas refutation over `CReal` end to end | `reconstruct_lra_proof` → `generalize_over_ordered_ring(SetoidInterface)`; exit criterion: footprint **0**, **39** binders, `residual_eq_constants` **0**, and the instantiation recovers a `CReal`-specific `False` | M | B |
| **D** | Decide what "retiring `real`" means, in an ADR | `build_creal_model_of_arith` and `build_int_model_of_arith` **both build the `Real` package** to compute their obligations from the axioms as they stand. Deleting the package deletes both relative-consistency results. The honest target is "no shipped proof route *reaches* the 30", which redefines the ledger metric from *declared* to *reached* | S (ADR) | C |
| **E** | Lean goldens + source pins | 2 goldens with `Real.` occurrences: `arithmetic-farkas-linear.lean` (**413**), `arithmetic-sum-of-squares.lean` (**24**); the third, `arithmetic-ordered-ring-farkas.lean`, has **0** and needs no rewrite. 3 source pins of the literal `Real.lt_irrefl`: `tests/lean_crosscheck.rs:3310`, `src/reconstruct/tests.rs:5207`, `scripts/check-lra-hypothesis-binding.py:335` | M | C |
| **F** | The axiom ledger | `docs/plan/lean-axiom-ledger-v1.json`: **30** entries, **30 of 30** `real`, **30** SHA-256 type bindings — plus **35** `retired_entries` and **10** declared `live_documents` that are extra invalidation surface. Consumers: **2** gate files (`scripts/check.sh` 207–208 and the `justfile` recipe, 4 invocation lines total — *not* 4 gate scripts), **2** Python test suites (`test_lean_axiom_ledger.py`, `test_lean_complete_parity.py`) and **3** further `.py` generators/checkers that read the JSON | M | D |
| **G** | The fact ledger | `F-schedule-critical-chain-infeasible.json`: **26**-entry footprint, **17** in the `Real` package (16 dotted + the bare carrier), `--expect-axioms 26` on **both** evidence commands. It already carries **stale prose**: `evidence[1].supports` and its `notes` still say "30 axioms" inside a 26-entry fact. Also `F-real-axioms-modelled-by-constructed-setoid.json` and `F-ordered-ring-farkas-refutation.json` | S | D |
| **H** | Docs | **31** markdown files assert `axiom=30` / `30 of 30` (30 under `docs/`, plus `PLAN.md`, which is generated). 3 further Rust doc-comment sites, 2 fact JSONs | M | D |

### The brief's counts, corrected

| Brief | Actual | |
|---|---|---|
| 57 files name `build_arith_prelude`/`ArithPrelude` | **38** (22 `.rs`, 16 `.md`, **0** `.lean`/`.py`/`.sh`/`.json`). The 57 is from `F-real-axioms-modelled-by-constructed-setoid.json` and counts files naming *`Real` symbols*, which today is **71** | ✗ |
| 13 rewrite-required `.rs` consumers (6 kernel, 7 solver) | **22** `.rs` name the package: **17 kernel**, **5 solver**. The solver's 7 is right only under a semantic grep (`\barith\.` too); the kernel's 6 is right only for `src/` non-test files excluding `arith_prelude.rs` itself — it omits 2 integration tests, 5 examples and 3 inline test modules | ✗ |
| `arith.logic` is the only route to `LogicPrelude` | True *inside* `reconstruct/arithmetic/` only. **4** solver sites already call `build_logic_prelude` directly (`reconstruct.rs:427`, `lex_reconstruct.rs:180`, `word_reconstruct.rs:274`, `regex_reconstruct.rs:232`), which *lowers* the re-plumbing cost. For `CReal` it is a 3-hop field path, `c.rat.int.logic` | ✗ |
| ~45 doc sites | **31** markdown (38 across all file types; 14 under the strictest pattern). 45 exceeds every pattern tried | ✗ |
| 30 `ArithPrelude` fields across 158 accesses | **158** confirmed (82 + 57 + 19), 31 distinct field names = 30 declarations + `logic` | ✓ |
| 3 goldens at 413 / 24 / 0 | confirmed exactly | ✓ |
| 26-entry footprint, 17 `Real.*`, `--expect-axioms 26` | confirmed | ✓ |
| ledger is 30 of 30 `real` with SHA-256 bindings | confirmed 30/30/30; but **2** gate files, not 4 | ~ |

### What does not exist yet, precisely

1. **`SetoidEq` cannot be supplied, only derived.** `LraReconstructCtx::setoid`
   is private and its only writer is `enable_setoid_equality`, which declares
   nine axioms and computes nine restatements by rewriting `Eq Real` out of the
   `Real` laws — hard-erroring if the rewrite does not fire. Slice B is exactly
   the missing constructor plus the guard that makes supplying one safe.
2. **The `Eq` universe argument is a literal `1` at 7 sites**
   (`arithmetic.rs:448/464/486`, `ordered_ring.rs:1214`,
   `setoid.rs:174/564/570/583`). `CReal` is `Sort 1`, so this blocks nothing
   today; guard 2 reports the level so a future carrier at another level fails
   loudly rather than silently mis-elaborating.
3. **No route retires the package while the models still build it.** Both
   `build_int_model_of_arith` and `build_creal_model_of_arith` call
   `build_arith_prelude` first, by design — the obligations are computed from
   the axioms *as they stand in the environment*. Slice D is a decision, not
   code.

<!-- plan-section: landed-changes -->

| 2026-08-18 | (pending) | `LraReconstructCtx`'s carrier is a parameter: `RingSignature` + `RingEquality` replace the by-value `ArithPrelude`, `with_ring_signature`/`try_new` replace the panicking constructor, and five mutation-verified guards check a signature against the kernel. `CReal` passes them today with `CReal.Equiv` in the equality slot. Baseline output byte-identical. |
