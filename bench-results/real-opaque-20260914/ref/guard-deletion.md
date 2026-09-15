# Guard deletion: the matrix, and the two rounds it took to get one

Harness: [`../guard-deletion.py`](../guard-deletion.py). Raw:
[`guard-deletion.json`](guard-deletion.json). Each row is a real edit, a real
`cargo test` over BOTH halves of the registered suite, and a restore verified by
`git diff --exit-code`.

## Round 1 — five survivors out of five

The first run, against the integration suite alone:

| guard | killed |
|---|---:|
| G1 `replayed_sat` | **0** |
| G2 `simplex_fallback` | **0** |
| G3 `dpll_lia` support fast path | **0** |
| G4 `dpll_lia` full path | **0** |
| G5 `real_model_oracle` | **0** |

Not because the guards were redundant. Because **every closure on this path
produces a non-`sat`**, so a `!matches!(result, Sat)` assertion passes with any
one of them deleted. The suite was testing the VERDICT; the guards are about
WHICH LAYER produced it. That is the same defect as "six of seven guards
removable with everything still green", arrived at from the other direction.

Two changes, and they are the transferable part:

1. **The sat-side tests now assert the decline BY NAME** —
   `assert_declined_by_the_opaque_real_gate` requires the `Unknown` detail to
   contain `opaque real UF applications or array reads`.
2. **The simplex guard was made to name itself.** It returned `Ok(None)` — this
   function's "I could not decide, try the elimination" — so deleting it merely
   moved the decline to the elimination's own replay and changed nothing
   observable. It now returns `Some(Decision::Incomplete(…))` with its own text,
   which is also **strictly cheaper**: the elimination would have decided the
   same abstracted system feasible and declined again.
3. `replayed_sat` and `simplex_fallback` are invisible from outside the crate by
   design (the entry point's type has no `Sat` variant), so they get lib-side
   unit tests that call `decide_within_with_options` directly.

## Round 2 — the matrix

| mutant | status | tests killed |
|---|---|---|
| **G1** `replayed_sat`'s `has_opaque_vars` | ok | **1** — `g1_fourier_motzkin_sat_over_an_abstraction_is_incomplete_not_sat` |
| **G2** `simplex_fallback`'s `has_opaque_vars` | ok | **1** — `g2_simplex_sat_over_an_abstraction_is_not_sat` |
| **G3** `dpll_lia` support fast path | ok | 3 |
| **G4** `dpll_lia` full path | ok | 3 (**the same 3**) |
| **G5** `real_model_oracle` → `real_theory_oracle` | **SURVIVED** | 0 |
| C1 = G3+G4 | ok | 3 |
| C2 = G3+G4+G5 | ok | 3 |
| C3 = every runtime guard | ok | 5 |

**G1 and G2 each kill exactly one test, and a different one.** That is the rule
satisfied literally.

**G3 and G4 kill the same three.** They are the two entry gates on one route and
this population reaches both; deleting either lets `try_finish_sat` run and the
decline then comes from sat-model reconstruction instead. Each is individually
load-bearing for the REASON; neither is individually load-bearing for the
verdict. Said plainly rather than counted as two.

**G5 survives, and it cannot be made not to.** `has_opaque_real_apps` is true on
exactly the atoms the opaque collector abstracts — the detector's arms are the
linearizer's arms, deliberately. So `has_opaque_real_apps == false` implies the
two oracles are the same function on that query, and no fixture can separate
them while G3 and G4 stand. G5 is the layer that catches a future widening of
the abstraction that the detector has not been taught about. **It is defence in
depth with no possible witness today, and recording that is more useful than
manufacturing a fixture that pretends otherwise.**

## What C3 proves, which is the thing worth having

C3 removes **every runtime guard** — both `has_opaque_vars` returns, both
`has_opaque_real_apps` gates, and the model oracle. The verdict is still
`Unknown`:

```
linear-arithmetic sat-model reconstruction declined in the real theory:
lra: sat model replay could not be verified (assertion #17):
no interpretation bound for function #0
```

Two closures survive every local edit:

- **The model replay** (`replayed_sat`, the shipped trust anchor for `sat` on
  this route, untouched by ADR-2065). A model over an abstracted system does not
  bind the opaque terms, so replaying the ORIGINAL assertions cannot evaluate.
- **The type.** `check_with_lra_opaque_apps_within` returns `LraOpaqueOutcome`,
  which has `Unsat` and `Undecided` and nothing else. **There is no single-hunk
  mutant of this design that yields a wrong `sat`**, and the mutant that would —
  re-typing the oracle's outcome so it can carry a model — does not compile.
  That is what the type was for, and it is the one layer the matrix cannot
  score, because "cannot be deleted" is not a row.

## Method notes

- The harness's exit status depends on the finding: a survivor is exit 1.
- Anchors are asserted unique before mutating; a non-unique anchor is reported
  as `ANCHOR-NOT-UNIQUE(n)`, never silently skipped.
- Every file is restored with `git checkout HEAD --` and the restore is
  **verified**, not assumed.
- Run in this lane's own worktree, never the shared checkout.
