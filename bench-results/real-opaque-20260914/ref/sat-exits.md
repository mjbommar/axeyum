# The `Sat` exits, enumerated and closed

Raw output: [`sat-exits.txt`](sat-exits.txt) (regenerate with
`bash bench-results/real-opaque-20260914/sat-exits.sh`). Commit `7df00fd82`.

**Method.** By CONSTRUCTION SITE, not a `?`-scan — ADR-1966 enumerated 72
refusal-propagation sites and found a `?`-only scan under-reports by half. The
abstraction is a field on `lra::Collector` that is `false` on every
`Collector::default()`, so the question "where can an abstracted system reach a
`Sat`?" reduces to a four-step closure over construction sites and callers.

## The instrument lied once, and the control was counting lines

The first version of the enumerator excluded test code by cutting each file at
its **first** `^#[cfg(test)]` line, on the usual assumption that it marks the
test module at the end. In **both** files it marks a test-only helper item in
the middle — `lra.rs:2482`, `dpll_lia.rs:1730` — so the cut discarded **2,397
and 3,133 lines of production code**, including a whole `CheckResult::Sat`
construction (`check_with_lra_simplex`, `lra.rs:3833`) and both real theory
oracles. The output looked clean and complete. It was a measurement of the
accepted subset.

`satexits.py` now excludes each `#[cfg(test)]` region by brace balance, prints
`raw` / `in_test` / `production` and **asserts they sum**, and hard-fails on a
shape it cannot parse rather than skipping it. `lra.rs` has **six** such
regions, not one.

## E1 — every construction site of `lra::Collector` in the workspace: 2

| site | flag |
|---|---|
| `lra.rs:541` (`collect_constraints_with_options`) | the argument — the ONLY setter |
| `lra.rs:3800` (`check_with_lra_simplex`) | `Collector::default()` ⇒ `false` |

## E2 — callers of the setter: 2, and one discards the verdict

| caller | value | can it produce a verdict? |
|---|---|---|
| `collect_constraints` (`lra.rs:519`) | `false` | — |
| `decide_within_with_options` (`lra.rs:627`) | the argument | yes |
| `atom_in_lra_opaque_fragment` (`lra.rs:2152`) | `true` | **no** — `.map(\|_\| ())`, a membership test |

Callers of `decide_within_with_options`: `decide_within` (`false`) and
`check_with_lra_opaque_apps_within` (`true`). **One decision function is
reachable with the abstraction on.**

## E3 — every `Sat` construction in the two files: 9 in production

`lra.rs` — 3 `Decision::Sat` + 2 further `CheckResult::Sat`:

| site | function | reachable with an abstracted system? | closure |
|---|---|---|---|
| `lra.rs:153` | `check_with_lra_within_certified` | **no** — consumes `decide_within`, flag `false` | structural |
| `lra.rs:868` | `replayed_sat` | **YES** | `has_opaque_vars()` at `lra.rs:838`, **before the model is built** |
| `lra.rs:1057` | `simplex_fallback` | **YES** | `has_opaque_vars()` at `lra.rs:1034` |
| `lra.rs:2612` | `lia_simplex_capped` | no — the INTEGER collector; its own `has_opaque_vars` downgrade, shipped, unchanged | pre-existing |
| `lra.rs:3833` | `check_with_lra_simplex` | **no** — `Collector::default()` | structural |

`dpll_lia.rs` — 6 `CheckResult::Sat`:

| site | what it is | closure |
|---|---|---|
| `371` | `certify_arith_dpll_unsat` forwards the loop's result | inherits the loop's two gates |
| `668` | forwards the **integer online CDCL(T)** probe (`lia_theory`) | different engine; no real collector |
| `1243` | the **propositional** skeleton model inside the loop | not a theory model, never returned |
| `3205` | `try_finish_sat` | three closures, below |
| `3339` | `theory_model` — the model oracle | real side uses `real_model_oracle` (unabstracted) |
| `3381` | the propositional SAT adapter | not a theory model |

Predicted (P1) "under 10 sites". Measured **9**.

## E4 — the three closures on the one exit that matters

`try_finish_sat` is where a real theory model becomes a `sat`. It is closed
three independent ways, and the guard-deletion result (below) shows they are not
one guard wearing three hats:

1. **Before the call.** `ArithAbstractor::has_opaque_real_apps` at
   `dpll_lia.rs:1338` (support-set fast path) and `:1420` (full path) — the real
   mirror of `has_opaque_int_apps` one line above each.
2. **Inside the call.** Real sat-model reconstruction uses `real_model_oracle`
   (plain `check_with_lra_within`), **not** `real_theory_oracle`. On an opaque
   atom the unabstracted collector answers `Unsupported`, which the caller
   already degrades to `Unknown` (`sat_reconstruction_unknown`). Mirrors
   `int_model_oracle`, which exists for exactly this reason.
3. **After the call.** The combined model is replayed against the **original**
   assertions; an unbound opaque term makes `eval` fail and the attempt is
   `ReplayRejected`.

And the conflict-detection oracle — the one that reads the abstraction — cannot
express a `Sat` at all: `check_with_lra_opaque_apps_within` returns
`LraOpaqueOutcome`, whose variants are `Unsat` and `Undecided`. That is the
**fourth** closure and the only one a future edit cannot quietly remove, because
removing it does not compile.

## What the abstraction does NOT reach

- `lra_farkas_certificate_within`, `lra_unsat_core`, `check_with_lra_simplex`,
  `check_with_lra`, `check_with_lra_within`, `check_with_lra_within_certified` —
  all go through `decide_within`, flag `false`.
- **The Farkas certificate is never re-exported from the opaque path.** Its
  public `vars` field maps a dense column to a `SymbolId` and an opaque column
  has no symbol, so a consumer (the Craig interpolant extractor) would mis-read
  it. `FarkasCertificate::verify` does not read `vars`, so the self-check inside
  the decision is unaffected; only re-export is refused.
- `dl-online`. ADR-2050 §5 noted that its *simulated* abstracted file was
  decided by `dl-online`, a route EARLIER than the one that refuses, and left
  open whether a fix confined to the abstractor is the whole of it. **It is, and
  the reason is that the simulation rewrote the FILE.** In the shipped design
  nothing rewrites the query: the abstraction exists only inside one conjunctive
  oracle's column space and no other route ever sees an abstracted term. The
  open design question ADR-2050 raised is answered by placement, not by a guard.

## Two column-space corrections this uncovered

Both are identical with the abstraction off and both would have been wrong with
it on, which is why the control division has to execute this code:

- `nvars` came from `ctx.vars.len()` — symbol columns only. Now
  `ctx.variable_count()`.
- `simplex_fallback` keyed its model by POSITION in `vars` rather than through
  `var_index`. The two agree exactly when no opaque column exists.
