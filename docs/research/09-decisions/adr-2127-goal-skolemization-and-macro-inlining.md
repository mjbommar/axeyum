# ADR-2127: goal skolemization already ships; macro inlining is built, measured, and stays off

Status: proposed
Index-summary: Goal skolemization already ships and fires on 90 of 90; definitional macro inlining is built behind `AXEYUM_MACRO_INLINE` and stays OFF, because z3's own macro finder is net NEGATIVE (2 gained, 3 lost) over all 525 undecided Tier-1 files.
Index-status: proposed
Date: 2026-09-16

## Status

Accepted (2026-09-16). Lane QUANT-PREPROCESS.

## Context

`bench-results/dt-ground-probe-20260916/README.md` closed out ADR-2114's
`GROUND` attribution. ADR-2114 read z3 refuting 44 of 55 AUFDTLIRA cores and 39
of 79 originals with **both quantifier engines off** as evidence of a separable
ground part. DT-GROUND-PROBE stripped every quantified assertion from those 83
files and asked plain z3: **0 unsat, 83 sat**. So the refutation comes from
z3's *preprocessing of the quantified assertions*, before `smt.ematching` and
`smt.mbqi` are consulted, and the probe named two mechanisms:

1. **Skolemizing an existential at positive polarity** — in this corpus almost
   always the SPARK convention `(assert (not (forall (...) body)))`.
2. **Folding a definitional `forall`-equality into a ground macro** and
   inlining it.

This lane was asked to build both behind one dated lever and measure them.

## Decision

1. **Do not build goal skolemization.** It already ships, and it already fires
   on every file this question is about. Measured, not inferred.
2. **Build definitional macro finding and inlining** — it genuinely did not
   exist — behind `AXEYUM_MACRO_INLINE`, **shipped OFF**, and **keep it off**:
   the mechanism's measured value on this population is *negative*.
3. Do not implement quasi-macros. The census puts them at 43 of 525 undecided
   files, 184 of those in one division, and the simple-macro measurement below
   removes the reason to go further.

## What the measurements say

### 1. Goal skolemization already ships, and already fires

`crates/axeyum-solver/src/quant_skolemize.rs` is a polarity-aware
NNF + Skolemize + prenex pass over the **whole assertion set**, emitting Skolem
*functions* over enclosing universals, wired into the ladder at
`crates/axeyum-solver/src/auto.rs` inside `prove_unsat_by_ematching`.

`bench-results/quant-preprocess-20260916/skolem-reach-probe.sh` measures
whether it fires, reading the pass's own `AXEYUM_QPROBE` instrumentation rather
than inferring from verdicts. Over 90 undecided files, 30 each from AUFDTLIRA,
UFLIA and UF:

| | count |
|---|---:|
| `skolem-bail` (abandoned an assertion at the mixed-polarity corner) | **0 of 90** |
| `skolemize-unchanged` (ran and changed nothing) | **0 of 90** |
| reached the e-matching retry at all | 86 of 90 |
| **residual quantifier still survived skolemization** | **86 of 86** |

The instantiation loop then exits on the clock: 59 `timeout-mid-round`, 2
`timeout-round-head`, 23 `CLOCK`.

So skolemization is not the gap on this population. **The census's
414-of-525 "has a skolemizable position" is a description of the corpus, not
headroom** — the shape is there and it is already being exploited.

### 2. The census: what the two shapes are worth as a ceiling

`scripts/quant-preprocess-census.py`, 1200 files (200 per division), 525
undecided by our ladder. Files carrying each shape, undecided in parentheses:

| division | files | undec. | top-level skolem pos. | deep | needs Skolem *fn* | ANY skolem | definitional macro | quasi-macro |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 81 | 159 (65) | 137 (51) | 10 (2) | 184 (74) | 22 (14) | 0 (0) |
| UFDTLIRA | 200 | 56 | 147 (43) | 88 (20) | 0 (0) | 162 (44) | 51 (7) | 0 (0) |
| UFLIA | 200 | 114 | 26 (22) | 81 (65) | 62 (51) | 83 (67) | 70 (44) | 6 (6) |
| AUFLIRA | 200 | 22 | 21 (6) | 160 (14) | 14 (4) | 164 (17) | 2 (2) | 184 (16) |
| UFNIA | 200 | 146 | 132 (93) | 47 (38) | 43 (34) | 166 (119) | 9 (8) | 1 (0) |
| UF | 200 | 106 | 42 (25) | 167 (93) | 156 (90) | 167 (93) | 87 (51) | 36 (21) |
| **total** | **1200** | **525** | (254) | (281) | (181) | **(414, 78%)** | **(126, 24%)** | (43) |

Two things worth carrying forward. `sk_conj` is **0 everywhere**: no assertion
in this corpus puts a negated universal under a top-level `and` — the goal is
always directly `(assert (not (forall ...)))`. And `macro_reject_occurs` is 0 in
five of six divisions (120 in UF alone), so on this corpus the occurs check is
almost never the condition that refuses a candidate; coverage is.

### 3. The first macro ablation was vacuous, and printed a clean-looking answer

`z3 smt.macro_finder=false` against plain `z3` reported `same` on **297 of 297
rows**. That is exactly what a working ablation with no effect prints, which is
the only reason it was checked.

It was measuring nothing. `smt_params::setup_AUFLIRA()` assigns
`m_macro_finder = true` **unconditionally**
(`references/z3/src/params/smt_params.cpp:420`), and the logic setup runs
*after* the command line is parsed. Every division here reaches that
assignment: `AUFLIRA` by name (`src/smt/smt_setup.cpp:188`), and
`AUFDTLIRA`/`UFDTLIRA` through `setup_unknown(static_features&)`
(`smt_setup.cpp:210`), whose quantified-and-contains-real branch calls
`setup_AUFLIRA(false)` (`smt_setup.cpp:845-847`). Both arms ran with macros
**on**. On UFLIA/UFNIA/UF the mirror image held — `setup_UFNIA` delegates to
`setup_AUFLIA` (`smt_setup.cpp`), which leaves the flag false because the
assignment is commented out at `smt_params.cpp:399-401` with the reason *"It
destroys the existing patterns"* — so both arms ran with macros **off**.

The obvious check passes and is useless: z3 **does** validate option names and
errors on an unknown one, so "the flag was accepted" was true the whole time.

The fix is `auto_config=false`, which routes to `setup::setup_default()`
(`smt_setup.cpp:69`) whose unmatched-logic branch is the static-feature-free
`setup_unknown()` (`smt_setup.cpp:805`) — it never touches `m_macro_finder`.

`bench-results/quant-preprocess-20260916/control/macro-finder-positive-dt.smt2`
pins the discrimination: under those flags with both quantifier engines off it
is `unsat` with `macro_finder=true` and `unknown` with `macro_finder=false`.
**The ablation script now runs that control first and exits 4 before writing a
single row if the arms agree**, so this failure cannot recur silently.

### 4. The corrected ablation: macro finding is net NEGATIVE here

One binary, two arms (`auto_config=false smt.macro_finder=true|false`), back to
back on the same file on the same pinned core, arm order alternating per file,
12 s / 8 GiB, s7 cores `1,9` and `3,11`. Population: the files **our** ladder
leaves undecided.

| division | n | unsat (macro on) | sat (macro on) | LOST without macro | GAINED without macro | sat/unsat disagreement |
|---|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 81 | 57 | 0 | 0 | 0 | 0 |
| AUFLIRA | 22 | 18 | 0 | 0 | 0 | 0 |
| UFDTLIRA | 56 | 14 | 25 | 1 | 0 | 0 |
| UFLIA | 114 | 52 | 1 | 1 | 0 | 0 |
| UFNIA | 146 | 59 | 2 | 0 | **3** | 0 |
| UF | 106 | 13 | 0 | 0 | 0 | 0 |
| **total** | **525** | 213 | 28 | **2** | **3** | **0** |

**520 of 525 rows are identical between the arms. Macro finding decides 2 files
that are lost without it, and LOSES 3 files that turning it off recovers. Net
−1 of 525.** Zero sat/unsat disagreements anywhere: no soundness incident in
either arm. This is the COMPLETE undecided population of all six divisions --
not a prefix of a path-sorted list.

All three GAINED-without-macro files are in **UFNIA** — which is precisely the
division z3's own authors commented the flag out for, giving the reason *"It
destroys the existing patterns"* (`smt_params.cpp:399-401`). The measurement
reproduces their stated reason independently, on a population they never ran.

Note the denominator this is a ceiling *for*: z3 already decides **241 of these
525 files** that our ladder does not. Macro finding accounts for 2 of those 241,
and costs 3 elsewhere.

## The pass, and the criteria at `file:line`

`crates/axeyum-solver/src/quant_macro_inline.rs`. Every condition is z3's, and
every one is soundness rather than taste:

| condition | z3 | why it is soundness |
|---|---|---|
| uninterpreted head | `macro_util.cpp:142` | a theory symbol already has a meaning |
| arity **==** binder size | `macro_util.cpp:143` | `>=` is the quasi-macro relaxation |
| arguments are **distinct** bound variables | `macro_util.cpp:147-152` | `∀x. f(x,x) = t` constrains only the diagonal; rewriting `f(a,b)` is a **wrong unsat** |
| arguments **cover** the binder | derived by pigeonhole, `macro_util.cpp:135-137` | an uncovered binder variable makes the assertion a constraint on `t`, not a definition |
| **occurs check** | `macro_util.cpp:182`, `:222`; `occurs.cpp:76-85` | `∀x. f(x) = g(f(x))` is recursive, not definitional |
| **acyclicity over the definition SET** | `macro_manager.cpp:130-134` | two definitions that each pass the occurs check can still close a loop |
| a symbol defined **twice** is refused | `macro_manager.cpp:120-123` | the second assertion is a real constraint |

Boolean `↔` needs no branch: `iff` is `Eq` at Bool sort, in this IR as in z3
(`ast.h:2197`). The negated-Bool-equality form has an explicit branch in z3
(`macro_util.cpp:187-193`) and is counted by the census. Unit literals
`∀x̄. f(x̄)` / `∀x̄. ¬f(x̄)` are **not** macro-finder shapes at all — only
`quasi_macros::is_quasi_macro` handles them (`quasi_macros.cpp:176-186`) — so
the census gives them their own column rather than crediting the macro finder
with a rewrite it never performs.

Parameters are recorded in the head's **argument** order, not the binder's:
`∀x y. f(y, x) = y` is legal and binder order would silently swap the actuals.
z3 handles this with `normalize_expr` (`macro_util.cpp:503-538`).

cvc5's equivalent is `theory/quantifiers/quantifiers_macros.cpp` (not
`preprocessing/passes/quantifier_macros.cpp`, which no longer exists): head
recognition at `:158` `isBoundVarApplyUf`, occurs check at `:108`
`containsBadOp`, coverage at `:270-279` via a free-variable check on the
constructed lambda. Gated by `--macros-quant`, **default false**
(`options/quantifiers_options.toml:1785`), and force-disabled for HOL and
sygus. Both reference solvers ship this pass off by default.

### Soundness, and what does not transfer

Under all the conditions above, inlining is an **equivalence**, so `unsat`
transfers back to the original unconditionally.

`sat` does **not** transfer, for a project reason rather than a mathematical
one: every `sat` must be checkable by evaluating the *original* term against
the lifted model (CLAUDE.md, Hard Rules), and the rewritten query's model has
no interpretation for `f` at all. Recovering one is model reconstruction this
module does not do. `MacroInlining::sat_transfers` reports this at the
producer so the call site reads the answer instead of restating it.

The wiring is a **prefix, not a replacement**: the inlined query is tried
first, only an `unsat` is taken, and anything else falls through to the
original assertions. So shipped behaviour is a floor even when the lever is
armed.

## Mutation controls, and one guard that measured redundant

Run in a `scripts/lane-snapshot.sh` copy, in the ARMED arm, both suites.

| mutation | tests that die |
|---|---|
| drop the ACYCLICITY check | **exactly one**: `mutually_recursive_definitions_are_refused_by_the_cycle_check` |
| drop the ARITY `== binder size` check | **exactly one**: `a_binder_variable_missing_from_the_head_is_refused` |
| weaken DISTINCTNESS (`||` -> `&&`) | 9 unit + 3 route; a blunt mutation that also breaks the positive path, so it kills loudly rather than cleanly |
| drop the OCCURS CHECK | **ZERO** |

The last row is a finding, not a gap to paper over. **The acyclicity check
subsumes the occurs check**: `f` occurring in its own body is a self-loop in
the dependency graph, so the graph check refuses it first. No fixture can
separate them in this IR, because a function can only occur as an application
-- there is no shape that is a self-occurrence and not a self-loop.

Two consequences were applied rather than noted. The check is kept (it is z3's
own condition at the same point, and it rejects locally before a graph is
built) but the code now says it is subsumed, so it does not read as protection
it does not provide. And the unit test formerly called
`occurs_check_refuses_a_recursive_definition` is renamed
`a_recursive_definition_is_refused_though_acyclic_is_what_refuses_it`: a test
whose name misattributes which guard it pins is exactly how a redundant guard
goes on looking load-bearing.

## Why the lever is not in `config_registry`

`config_registry`'s `every_entry_names_a_live_constant` requires the entry's
`name` to exist as a **constant** at the named module. `AXEYUM_MACRO_INLINE`
gates a pass, not a numeric bound, so it is a `OnceLock<bool>` function and has
no constant to name — registering it would fail that test. This follows the
existing precedent for boolean pass gates (`AXEYUM_ZERO_INST_SKELETON` at
`auto.rs`, likewise unregistered). `cap_lever!` does not apply: it parses
numerics.

## Consequences

- The lever stays **OFF**. Anyone re-opening this should re-read the table in
  §4 before building, not the census in §2: the census counts *shapes*, and the
  ablation measures what the shape is *worth*.
- The ablation harness is reusable and now refuses to produce vacuous rows. Any
  future "does z3 option X matter" question should copy its control discipline,
  and specifically should check whether the logic setup overwrites X.
- **The open question this lane did not answer** is the one the skolem-reach
  probe surfaced: a universal survives skolemization on 86 of 86 files and the
  instantiation loop then dies on the clock. That, not preprocessing, is where
  this population is lost. Lane QUANT-GROUND-INCREMENTAL is on the adjacent
  half (the ground closure after activation, ADR-2120 §7).

## Alternatives considered

- **Ship it ON for AUFDTLIRA/UFDTLIRA only**, where z3 enables the macro finder
  and where it costs nothing. Rejected: it gains nothing there either (0 of 137
  rows move), so the only effect would be added surface.
- **Implement quasi-macros.** Rejected: the simple-macro ceiling is already
  measured negative, and the quasi path is strictly more machinery (it emits a
  guarded `ite` with a fresh `f_else`, `quasi_macros.cpp:259-270`) with an
  additional global `is_unique` precondition (`quasi_macros.cpp:80-82`).
- **Delete the pass rather than land it off.** Rejected: the measurement is the
  deliverable and a reader who wants to re-run it needs the code. It is inert
  behind the lever and carries its own soundness fixtures.

## References

- `bench-results/quant-preprocess-20260916/` — census, ablation, skolem-reach
  probe, positive control.
- `bench-results/dt-ground-probe-20260916/README.md` — the finding this builds
  on.
- ADR-2114, ADR-2113, ADR-2120 — the quantified engine's three traces.
