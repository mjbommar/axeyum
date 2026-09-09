# The SAT/SMT solver stack — a comprehensive inventory (2026-09-09)

This folder is a module-level inventory of the axeyum SAT/SMT solver stack and
the pre- and post-processing workflows around it: the front end and rewriting
that run before a theory solver sees a problem, the solvers themselves, and the
models, proofs, certificates and evidence produced after a verdict.

Base commit: `ea8515407`. Every file here was produced by reading source, not by
running the build. Claims that would need a build to confirm are marked
`[unverified]` in the file that makes them.

## Why this exists

The existing documentation covers this ground thinly. `docs/internals/rewriting.md`
is 67 lines against a 17k-line crate with 16 passes; `docs/reference/support-matrix.md`
is 38 lines and had not been touched since 2026-08-07. The nine area files below
each carry a **Doc drift** section auditing the existing doc for their area
against the source.

## The honesty axis

Every component in every file is classified by **reachability**, because a
300k-line solver crate accumulates modules that compile but that no dispatch
path can select:

| Label | Meaning |
|---|---|
| `WIRED` | Reachable from a public entry point, with the caller site cited |
| `TEST-ONLY` | Only callers are under `#[cfg(test)]`, `tests/`, `benches/`, `examples/` |
| `FEATURE-GATED` | Reachable only under a non-default feature other than `full` — `z3`, `bench-internals`, `batsat-reference` |
| `NO CALLER FOUND` | Searched, nothing found; the file states exactly what was searched |

`full` is the assumed baseline throughout (see the feature profile below), so it
is not used as a FEATURE-GATED label — it would apply to almost everything and
carry no information.

## The files

| File | Area | Layer |
|---|---|---|
| [01-sat-core-and-cnf.md](01-sat-core-and-cnf.md) | CDCL core, DRAT/LRAT, inprocessing, XOR/Gaussian, AIG, bit-blasting | propositional |
| [02-frontend-ir-and-rewriting.md](02-frontend-ir-and-rewriting.md) | SMT-LIB parser, term IR, query object, the 16 rewrite passes | **pre-processing** |
| [03-dispatch-routing-and-backends.md](03-dispatch-routing-and-backends.md) | Solver facade, dispatch decision tree, portfolio, capabilities, backends | spine |
| [04-arithmetic-theories.md](04-arithmetic-theories.md) | CDCL(T) loop, simplex, LRA/LIA/NRA/NIA, difference logic, BMC/IMC/PDR | theory |
| [05-bitvector-arrays-fp-and-datatypes.md](05-bitvector-arrays-fp-and-datatypes.md) | Lazy/eager BV, arrays, floating point, datatypes, cardinality, MaxSAT | theory |
| [06-euf-and-quantifiers.md](06-euf-and-quantifiers.md) | EUF, congruence closure, e-graphs, the ~45-file quantifier family | theory |
| [07-strings-and-regex.md](07-strings-and-regex.md) | Word equations, arrangements, derivative-based regex, Unicode surface | theory |
| [08-models-proofs-and-evidence.md](08-models-proofs-and-evidence.md) | Models, Alethe, kernel reconstruction, interpolants, the trust ledger | **post-processing** |
| [09-harnesses-benchmarks-and-gates.md](09-harnesses-benchmarks-and-gates.md) | Bench harness, scenarios, test census, feature-gate-to-zero audit, gates | measurement |
| [10-verification-log.md](10-verification-log.md) | Which lane claims the coordinator re-checked, and the four checks that changed a result | audit |
| [11-wiring-and-integration.md](11-wiring-and-integration.md) | Is it all actually wired up? One uniform measurement, and the nine integration gaps that matter more than dead code | audit |

## The other half: how we compare

[`docs/solver-comparison-2026-09/`](../solver-comparison-2026-09/00-README.md)
inventories the reference SAT/SMT solvers against the same subject matter, and
[its gap analysis](../solver-comparison-2026-09/10-gap-analysis.md) joins the
two; [the roadmap](../solver-comparison-2026-09/11-roadmap-and-plan.md) turns
both into ordered work with exit criteria. Its headline bears on how you read this folder: the largest gaps against
the reference solvers are not missing capability but capability recorded here as
built-and-unwired.

## Workspace census

Measured at `ea8515407` by counting files under `crates/*/src` and `crates/*/tests`:

| Quantity | Count |
|---|---|
| Workspace member crates | 27 |
| Lines under `crates/*/src` | 1,553,892 |
| Lines under `crates/*/tests` | 224,794 |
| Test files workspace-wide | 549 |

Largest crates by source lines: `axeyum-lean-kernel` 806,612 (out of scope here
— the proof kernel, not the solver); `axeyum-solver` 303,322; `axeyum-cas`
155,585; `axeyum-cnf` 48,355.

## Crate dependency layers

Derived from the `[dependencies]` section of each crate's `Cargo.toml`. `*`
marks a dependency that is `optional = true`.

```
layer 0  no axeyum deps
         axeyum-arith   axeyum-aig   axeyum-egraph   axeyum-lean-kernel
         axeyum-machine   axeyum-property-macros   axeyum-verify-macros

layer 1  axeyum-ir  <- arith

layer 2  axeyum-bv      <- aig, ir          axeyum-cnf   <- aig
         axeyum-query   <- ir               axeyum-rewrite <- ir
         axeyum-strings <- ir               axeyum-fp    <- arith, ir
         axeyum-cas     <- ir, arith

layer 3  axeyum-smtlib      <- fp, ir, strings      (all three NON-optional)
         axeyum-scenarios   <- ir, query
         axeyum-search      <- cas, cnf             (no solver dependency)
         axeyum-lean-import <- lean-kernel

layer 4  axeyum-solver <- aig, bv, cnf, ir, query, rewrite
                          + cas*, egraph*, fp*, lean-kernel*, smtlib*, strings*

layer 5  consumers of the solver
         axeyum-property <- ir, property-macros, solver
         axeyum-bench    <- cnf, ir, query, rewrite, scenarios, smtlib, solver
         axeyum-evm      <- ir, solver, property
         axeyum-verify   <- ir, solver, smtlib, property, verify-macros
         axeyum-machine-evidence <- ir, machine, solver
         axeyum-py       <- 13 crates          axeyum-wasm <- smtlib, solver
```

Two structural facts follow from this graph and are worth stating up front.

**`axeyum-search` bypasses the solver.** It depends on `axeyum-cas` and
`axeyum-cnf` only — not on `axeyum-solver`, `axeyum-ir`, or `axeyum-smtlib`. It
is an application layer that builds CNF directly and drives the SAT core,
without a theory solver in the path. See
[09-harnesses-benchmarks-and-gates.md](09-harnesses-benchmarks-and-gates.md).

**The default build is much narrower than the crate suggests.** Six of
`axeyum-solver`'s twelve axeyum dependencies are optional and enabled only by
`full`: `cas`, `egraph`, `fp`, `lean-kernel`, `smtlib`, `strings`. In a default
build there is therefore no SMT-LIB parser, no string theory, no floating point,
no CAS, no e-graph and no proof kernel.

## Feature profile

From `crates/axeyum-solver/Cargo.toml`:

| Feature | Default | What it adds |
|---|---|---|
| `qfbv` | **yes** | The minimal pure-Rust scalar QF_BV surface. Adds no dependencies by itself; it makes consumer intent visible. |
| `full` | no | `cas`, `egraph`, `fp`, `lean-kernel`, `smtlib`, `strings`. The multi-theory product surface. |
| `z3` | no | The Z3 oracle backend against system libz3. Implies `full`. Bootstrap scaffolding under ADR-0002, not a product backend. |
| `z3-static` | no | Prebuilt static libz3 for CI hosts without libz3-dev. Implies `z3`. |
| `batsat-reference` | no | Forwards to `axeyum-cnf/batsat-reference` so two measurement harnesses that time the demoted adapter can still run. See ADR-1703. |
| `bench-internals` | no | Re-exports crate-private `cdclt`/`simplex` internals for `benches/*.rs`. Implies `full`. Never enable outside a bench target. |

**The module-level consequence.** `crates/axeyum-solver/src/lib.rs:70` declares a
macro `full_modules!()` under `#[cfg(feature = "full")]`, invoked at
`lib.rs:251-252`, containing exactly 165 module declarations. The default build
compiles about a dozen modules: `backend`, `config_registry`, `error`, `incremental`,
`layers`, `lazy_smt_counters`, `live_instruments`, `memory_budget`, `model`,
`portfolio`, `proof`, `sat_bv_backend` and a few more. The public module groups
`theories`, `certificates`, `interpolation`, `optimization`, `verification` and
`constraints` are each `#[cfg(feature = "full")]`.

Note which side of that line the evidence machinery falls on: `model` and `proof`
are in the default set, while `certificates` and `interpolation` are not. What
that means for evidence in a default build is worked out in
[08-models-proofs-and-evidence.md](08-models-proofs-and-evidence.md).

The default build's freedom from any C or C++ dependency is a hard rule
(ADR-0002); `z3` is the only linked-solver dependency and it is an optional leaf.

## What the nine files found together

Each area file stands on its own. These are the patterns that only appear when
you read all nine, with the lane that found each. Every claim below was
re-checked by the coordinator against the cited lines, including positive
controls on the negative results.

### 1. Duplicate implementations of the same work

> **Corrected 2026-09-09.** This section was first published as "Duplicate
> implementations where the front door uses the untrusted one." Two of its three
> rows were wrong about WHICH side is trusted, and the error is recorded in
> [10-verification-log.md](10-verification-log.md) and in ADR-1810 / ADR-1811.
> The duplication is real; the framing was not. Corrected text follows.

Three lanes independently found the same shape: two implementations of one job,
where only one is reachable from the shipping path. What is NOT true in general
is that the reachable one is the weaker one — see the corrections below each row.

| Subsystem | Documented / evidence-carrying | What the front door uses |
|---|---|---|
| CNF inprocessing | `axeyum-cnf/src/inprocess.rs` (ADR-1750). Zero callers in `axeyum-solver` — this half stands. | Passes sequenced in `sat_bv_backend.rs:1827-2083`. **Correction:** this is the PROOF-CARRYING side. `ReductionLink` is `axeyum-cnf/src/reduction_link.rs:156` — the same crate as `inprocess.rs` — and since ADR-1780 (2026-09-08) the shipping path checks its `unsat` against the ORIGINAL formula through it (`sat_bv_backend.rs:2812`). `inprocess.rs` structurally cannot: it has no way to express the `compact()` renumbering the backend runs. |
| Word-level preprocessing | `preprocess.rs`, up to 8 rounds (`MAX_PREPROCESS_ROUNDS`, `:32`). Carries `real_div_zeros`, but has **no** function-interpretation loop. | `auto::preprocess_reduce` (`auto.rs:2158`), one straight-line round. **Correction:** it carries BOTH function interpretations (`:2335`) and `real_div_zeros` (`:2344`, since 2026-07-25) — a strict superset of the other pipeline's witnesses. |
| Bounded strings | `axeyum-solver/src/strings.rs` (`BoundedString`, 1,305 lines, public API), consumed only by `tests/strings.rs` | An independent encoder inside `axeyum-smtlib/src/parse.rs` |

**Corrected.** The first published version of this paragraph said "neither
preprocessing pipeline is a superset of the other" and that the front door does
not carry the `/0` witness. Both are false. `auto.rs:2344` carries
`real_div_zeros` — with the same comment as `preprocess.rs:221-224`, and since
2026-07-25 — and `auto.rs:2335` additionally carries function interpretations
that `preprocess.rs` never builds. The front door is the superset, and the
hazard the original text described has not existed for months.

How the error was made, since it is the more useful lesson: two passes verified
`preprocess.rs`'s witness loop and `auto.rs`'s pass ORDER, each in isolation, and
inferred an asymmetry from the pair. Neither checked whether `auto.rs` ALSO had
the witness. A partial view of each half is not a view of the whole.

The duplication itself is still real, and ADR-1811 decides it.

The strings case cannot be fixed by discipline: `axeyum-smtlib` does not depend
on `axeyum-solver`, so `parse.rs` structurally cannot call `BoundedString`. The
three mentions of it in `parse.rs` are comments.

### 2. Hand-written tables that dispatch never reads

Every table describing what the solver supports is a literal, and none is
derived from the code it describes:

| Table | Shape | Consulted by dispatch? |
|---|---|---|
| `SUPPORT_MATRIX` (`support_matrix.rs:177`) | 19-row `const` | No — zero occurrences in `auto.rs` or `smtlib.rs` |
| `CAPABILITIES` (`capabilities.rs:144`) | 105-row `const` | No — same |
| `ALL_TRUST_IDS` (`trust.rs:147`) | 15-element `const`, `is_certified` a hand-written `match` (`:322`) | n/a — 8 certified, 7 trust holes |

These are reporting surfaces. They can drift from the code without any gate
noticing, and `docs/reference/support-matrix.md` shows the failure mode: it
claims six columns against four in source, and was already wrong the day it was
written (`ee12f02aa`).

### 3. Checkers that cannot fail

The project's stated identity is "untrusted fast search, trusted small
checking," and its own contributor guide warns that a checker which cannot fail
is worse than none. Measured state:

- `tests/carcara_crosscheck.rs` and `tests/lean_crosscheck.rs` **skip and pass**
  when the external binary is absent, and `references/` is gitignored. The
  suite's own header says so: "A skipping suite is a suite that has never been
  shown to fail" (`carcara_crosscheck.rs:29-32`).
- `scripts/check-capability-assurance.py` **is** a registered gate
  (`check.sh:872`, `justfile:579`), but it classifies the free-prose `evidence`
  field by regex into an "external-artifact-checker" tier. It reasons about
  Carcara; it does not run Carcara.
- `just interpolant-certificate` (`justfile:1922`) is the counter-example done
  right — `AXEYUM_REQUIRE_DRAT_TRIM=1` makes the exit status depend on the
  finding. It is outside `just check`.

### 4. Eight unsat routes produce no checkable evidence

`Evidence::Unsat(None)` has exactly 8 construction sites in `evidence.rs`
(29 textual matches, less 16 comments, 3 in the test module, and 3 match arms):
NRA (`:3144`), the general `solve` fallback (`:3814`), the string front door
(`:4119`), difference logic above the certifying size (`:2596`), QF_BV export
declines on node/CNF/check budget (`:2162`, `:2282`, `:2348`), LRA without a
Farkas certificate (`:2406`), and CDCL(T) theory refutation (`:2643`).

These are labeled `"unsat-uncertified"` and never mislabeled — the honesty is
real. But for these routes the trusted-checking half of the identity is absent.
Separately, `QF_UFLRA`/`QF_UFLIA` unsat has an empty trust slot by construction,
because those routes call `CdclT` directly and `CdclT` emits no proof.

### 5. Public API with no caller

Roughly 4,200 lines of public surface have no production caller (the figure was 5,200 before `bitblast_miter` was found to be called from `axeyum-bench`). Each was found
with an explicit search and a positive control:

| Module | LOC | External references |
|---|---|---|
| `bitblast_miter.rs` | 1,030 | No caller inside `axeyum-solver`, but **it is called from outside**: `axeyum-bench/src/main.rs:5782` and `certificate_process.rs:170` use `certify_qf_bv_unsat_end_to_end_within`. Not dead — off the solve path, on the bench path. (Corrected 2026-09-09; see [10-verification-log.md](10-verification-log.md).) |
| `pdr_lia.rs` + `imc_lia.rs` | 1,771 | 4 `pub use` lines in `lib.rs` only |
| `strings.rs` (`BoundedString`) | 1,305 | test-only (see §1) |
| `prove_quant_unsat_alethe` | ~1,100 | no caller outside its own tests |
| `theory_combination` — 4 functions | — | zero; positive control `classify_interface_equalities` has 23 |

### 6. The shipped default is a thin slice

`crates/axeyum-solver/src/lib.rs:70` puts 165 modules behind one
`full_modules!()` macro gated on `full`. The consequences compound:

- The default `qfbv` build has no SMT-LIB parser, strings, floating point, CAS,
  e-graph, or proof kernel — all six are optional dependencies.
- It produces exactly two evidence artifacts: a replayed model and a DRAT/LRAT
  unsat proof. `Evidence`, Alethe, the ~55 typed certificates, interpolation and
  kernel reconstruction are all `full`-only.
- It runs **no CNF inprocessing at all**: `cnf_inprocessing: false`
  (`backend.rs:390`), and `cnf_vivify: true` is a documented no-op without it.
- 298 of 302 solver integration suites compile to zero tests on default
  features (268 need `full`, 28 need `full`+`z3`, 2 need
  `full`+`batsat-reference`). Only 4 run untouched.

That last number deserves care in both directions: it is the expected shape for
a crate whose theory surface is feature-gated, *and* it means the default-feature
test run exercises almost nothing.

### 7. Documentation drift is broad, and includes this file's own instructions

Confirmed drift, each cited line-against-line in the area files:
`docs/internals/cnf-and-sat.md` (RAT support, EMA restarts), `proof-stack.md`
(same RAT claim, found independently by a second lane), `rewriting.md` (eight of
sixteen files unmentioned, predates ADR-1721), `term-ir.md` and `evaluator.md`
(both say ADR-1702 slice 2 is unlanded; `Value::WideInt` exists),
`support-matrix.md` (column count), `solver-config.md` (`cnf_vivify` default),
`solver-dispatch.md` (names a type `SolveConfig` with zero hits),
`smtlib-support.md`, ADR-0009 (claims the `Solver` façade is "backed by a real
incremental engine"; `push`/`pop` is a `Vec` watermark at `solver.rs:126-142`
and `check` re-submits everything), and ADR-0010's stale "not yet" lazy-array
clause.

`CLAUDE.md:319` is itself stale: it says `axeyum-fp` "depends only on
`axeyum-ir`", but `crates/axeyum-fp/Cargo.toml` also depends on `axeyum-arith`.
Left unedited here — it is a shared file with concurrent writers.

### Two things that are in better shape than expected

Not everything measured badly, and saying so is part of an honest inventory:

- **No floating point touches an arithmetic verdict.** Zero `f64`/`f32` in all
  eleven `nia_*`/`nra_*` files and all of `axeyum-arith`, confirmed with a
  positive control (`cdclt.rs:282` `VSIDS_DECAY: f64` is found by the same
  grep). `nra_real_root.rs` is exact Sturm chains, resultants and CAD
  throughout.
- **The partial-operator fuzz rule is being followed for strings.** `str.at`,
  `str.substr`, `str.to_code`, `str.to_int` and `str.from_code` each have a
  dedicated degenerate-argument seed class, and the `\u{...}` escape hole from
  `ba0d9149` is closed by one shared decoder (`parse.rs:8900`). Integer
  `div`/`mod`-by-zero is likewise fuzzed at roughly 37% zero divisors.

## Method and limits

Nine parallel agents produced the area files, each restricted to source reading
— no `cargo build`, `cargo test`, or gate execution — with a shared method brief
requiring a `file.rs:line` citation for every non-obvious claim and an explicit
statement of what was searched whenever a negative result is reported.

The limits that follow from that method:

- **No claim here is confirmed by execution.** A cited call site shows a path
  exists in source; it does not prove the path is taken at runtime, and it does
  not prove the code is correct.
- **`NO CALLER FOUND` is a search result, not a proof of dead code.** Dispatch
  through a trait object, a macro, or a registry table can hide a caller from
  a textual search. Each file states its searches so a reader can judge.
- **The Lean kernel is out of scope.** `axeyum-lean-kernel` is 806k lines and is
  covered only at the interface the solver calls into.
- Line numbers are accurate at `ea8515407` and will drift.
