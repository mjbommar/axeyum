# Is everything we implemented actually wired up? (2026-09-09)

A direct answer to that question, measured uniformly. Base commit `ea8515407`
plus the corrections in [10-verification-log.md](10-verification-log.md).

The nine area files in this folder each report a reachability tally, but they
count different things — files, functions, dispatch routes — and share no
denominator. Summing them would produce a number that looks precise and means
nothing. This file measures one thing one way instead.

## Short answer

At module granularity, **161 of 176 modules in `axeyum-solver` are referenced by
another module**. About 11 are reachable only from the crate's own test suite.

That is the least interesting way to ask the question. The larger finding is not
dead code — it is a substantial amount of working code wired to something other
than the default solve path: to a config flag that defaults off, to the bench
harness, to the Python bindings, or to a second implementation that superseded
it without anything recording the decision.

## Method

For every `mod X;` declared in `crates/axeyum-solver/src/lib.rs` (176 — the
default set plus the 165 inside `full_modules!()`), search every *other* file in
the crate for either:

- the module path — `X::`, `use crate::X`, `use super::X`; or
- any item name that `lib.rs` re-exports from module `X`.

The second half is not optional. `evidence.rs:4376` calls
`crate::prove_qf_abv_unsat_alethe(...)` — the crate-root re-exported name — so a
module-path search alone reports that module absent. Getting this wrong is the
single most common way to manufacture a false "this is dead" finding in this
repository; it happened five times in the session that produced this folder.

Limits: this is a source-level textual measurement with no build and no run.
Dispatch through a trait object, a macro, or a registry table can hide a caller.
It sees modules, not functions, so dead functions inside live modules are
invisible to it.

## Result

| | Count |
|---|---|
| Modules declared in `lib.rs` | 176 |
| Referenced by at least one other module | 161 |
| Referenced by no other module | 15 |

Resolving those 15 against consumers outside the crate:

| Module(s) | Reached from | Verdict |
|---|---|---|
| `solver` | 44 solver test files, 8 other crates | It *is* the public façade. Expected. |
| `strategy` | `axeyum-py/src/solver/core.rs:201` | Reachable only from the Python bindings, not from Rust dispatch |
| `bitblast_miter` | `axeyum-bench/src/main.rs:5782`, `certificate_process.rs:170` | Reachable only from the bench binary |
| `aufbv` | `axeyum-bench/examples/route_solo.rs` | Reachable only from a bench example |
| `abduct`, `enums`, `faithfulness`, `horn`, `hypothesis_min`, `imc_lia`, `lex_reconstruct`, `pb`, `pdr_lia`, `records`, `toy_bv_vm` | solver `tests/` only | Test-only |

Apparent references from `axeyum-cas` and `axeyum-lean-kernel` are name
collisions — neither crate depends on `axeyum-solver`, so neither can call it.

**11 of 176 modules (6%) are test-only.** Treat that as a floor. The area files
found dead *functions* inside live modules that this measurement cannot see: all
seven `*_certified` interpolant variants, four `theory_combination` functions,
`prove_quant_unsat_alethe` (~1,100 lines), `pass_stats.rs` (345),
`algebraic_bridge.rs` (343).

> **Corrected 2026-09-10.** The counts below UNDERCOUNT. Roadmap item 2.7
> reimplemented this method rather than trusting it and found two bugs in it,
> each of which changed an answer:
>
> 1. **String literals must be stripped over the whole text, not per line.** A
>    Rust literal continues across lines with a trailing backslash, so a
>    line-wise strip leaves `capabilities.rs`'s prose tables looking like code.
>    That alone made `pdr_lia`, `imc_lia`, `horn` and `hypothesis_min` read as
>    WIRED in the corrected run's own first pass.
> 2. **A bare identifier is not an import.** `quant_bool_model_sat.rs` defines
>    its own `const MAX_CANDIDATES`, which is also `abduct`'s re-exported name.
>
> With both fixed, the base figure is **20 test-only modules, not 15** — part
> stricter method, part drift (176 modules declared when this was written, 184
> now). Every module this file named is confirmed test-only, so none was an
> artifact; the error was omission, not invention. `pdr_lia` and `imc_lia` have
> since been wired (item 2.7) and the remainder carry labels enforced by
> `tests/test_only_module_labels.rs`.

> **A note on `horn.rs`, added 2026-09-10.** Roadmap item 2.7 fixed
> `state_class`, which had mapped an all-`Int` predicate vocabulary to
> `Unsupported` and so left `pdr_lia`/`imc_lia` (1,771 lines) with no caller.
> That fix is real. It is also NARROWER than first reported: `solve_horn` itself
> has no caller in `src/` **by design** (`horn.rs:164` — it is a front-end whose
> caller is the library user), and `auto.rs` contains `horn`/`chc` zero times.
> So the engines are reachable through the public Rust API, and no SMT-LIB input
> routes to them. The wiring that would change that is an SMT-LIB CHC front
> door, which does not exist. See item 3.7's measurement.

## The integration gaps that matter more

Ranked by how much working capability each one keeps out of a default run.

| # | Gap | Evidence |
|---|---|---|
| 1 | **CNF inprocessing is wired but off.** Subsumption, vivification, BVE, compaction and XOR propagation do nothing in a default run. | `cnf_inprocessing: false`, `backend.rs:390`; `cnf_vivify: true` is a documented no-op without it |
| 2 | **The proof-carrying inprocessing module is unreachable.** The front door hand-rolls the same three passes with a different certificate mechanism. | `axeyum-cnf/src/inprocess.rs` has no caller outside its own crate's tests; the shipping copy is `sat_bv_backend.rs:1827-2083` |
| 3 | **Two preprocessing pipelines, neither a superset.** The 8-round one carries `real_div_zeros` model witnesses; the front door's single-round one does not. | `preprocess.rs:32` vs `auto.rs:2158`; `preprocess.rs:221-224` calls dropping that witness "a wrong `sat`" |
| 4 | **`Solver` push/pop is not incremental.** A `Vec` watermark, and `check` re-submits everything. | `solver.rs:126-142`, `:161-163`. ADR-0009 claims a "real incremental engine" |
| 5 | **The support matrix and capability table are not wired to dispatch.** They are reporting surfaces that can drift silently. | `SUPPORT_MATRIX` (19 rows), `CAPABILITIES` (105 rows): zero occurrences in `auto.rs` or `smtlib.rs` |
| 6 | **External proof checkers are not wired to any gate.** | `carcara_crosscheck.rs`, `lean_crosscheck.rs` skip and pass when the binary is absent |
| 7 | **Eight unsat routes produce no checkable evidence.** Correctly labeled, never mislabeled — but the checking half is absent. | 8 `Evidence::Unsat(None)` construction sites |
| 8 | **The portfolio's fused group is runtime-dead by default.** | `portfolio::FusedGroup` needs `AXEYUM_PORTFOLIO_WORKERS >= 2`; default is 1 |
| 9 | **The quantified ladder has no route trace.** A quantified file's route attribution names whichever QF sub-route it reached. | `auto.rs:492-1108` records nothing; eleven rungs report only to stderr under `AXEYUM_QTRACE` |

## What a default build actually reaches

`full_modules!()` (`lib.rs:70`) puts 165 of the 176 modules behind the `full`
feature, so in the default `qfbv` profile they are not compiled at all.

A default `Solver::check()` therefore reaches about a dozen modules; has no
SMT-LIB parser, strings, floating point, CAS, e-graph or proof kernel; runs no
CNF inprocessing; and can emit two evidence artifacts — a replayed model and a
DRAT/LRAT unsat proof. 298 of 302 solver integration suites compile to zero
tests on default features.

None of that is wrong on its own; a feature-gated theory surface is a normal
design. It is recorded here because the gap between "implemented" and "reached
by a default run" is much wider than the module-level 6% suggests, and every
claim about what this solver does needs to say which profile it means.
