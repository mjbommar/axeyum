# Notes: 218-creal-build-bisect

Detail moved out of [`../status/218-creal-build-bisect.md`](../status/218-creal-build-bisect.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`creal.rs`'s `STEPS` table (194 entries) is run as a loop by
`build_creal_prelude_uncached`, so a throwaway `Instant::now()` around
`(step.run)` gives the whole distribution in **one run** — no 370-commit
bisect. A second throwaway patch timed `Kernel::check_declaration` per
declaration and recorded each term's DAG size.

Per-module (steps sum to 101.25 s of a 107.12 s instrumented run; the rest is
`build_rat_prelude` plus interning, outside the loop):

| module | s | % | steps |
|---|---|---|---|
| `trig_fn` | 59.24 | 58.5 | 14 |
| `cos_sign` | 11.46 | 11.3 | 6 |
| `uniform_convergence` | 8.32 | 8.2 | 9 |
| *everything else* | 22.2 | 21.9 | **165** |

`integral`, the largest family by count, is **4.82 s over 46 steps**.

Per declaration, with the sub-step split and term size:

| declaration | s | phase | inferVal | defeq | DAG nodes |
|---|---|---|---|---|---|
| `CReal.sinFnUniformConverges` | 11.65 | `trig_fn::declare_sin_fn` | 0.00 | **11.51** | 2,807 |
| `CReal.sinFn` | 11.56 | same step | **11.13** | 0.00 | 3,076 |
| `CReal.sinDominant16Over25CauchyBody` | 10.51 | `declare_sin_fn_dominant` | 10.39 | 0.00 | 2,349 |
| `CReal.cosWideNonpositive` | 9.86 | `cos_sign::declare_cos_wide_nonpositive` | 9.74 | 0.00 | 864 |
| `CReal.weierstrassMTest` | 8.17 | `uniform_convergence` | 7.64 | 0.00 | 2,038 |
| `CReal.cosDominant16Over25CauchyBody` | 6.01 | `declare_cos_fn_wide_progress` | 5.72 | 0.00 | 2,355 |
| `CReal.cosFnWideUniformConverges` | 5.05 | `declare_cos_fn_wide` | 0.00 | 4.80 | 2,657 |
| `CReal.cosFnWide` | 4.90 | same step | 4.65 | 0.00 | 2,926 |

**Eight declarations = 67.75 s of 94.22 s** across 1,559 declarations.

All three files were **added on 2026-08-27**: `uniform_convergence.rs`
(`edb2feb7b`, 05:06), `trig_fn.rs` (`7e0ccc952`, 12:40), `cos_sign.rs`
(`f69c51f3a`, 23:15).

## 3. It is not the `Definition`-unfold mechanism

`CLAUDE.md` names one way to lose an order of magnitude here — relating a value
produced by a `Definition` to a value you rebuilt yourself, forcing a full delta
unfold. **Checked, and refuted**, by counting δ-unfolds and unfold *attempts*
per declaration:

| declaration | successful δ-unfolds | `unfold_def` attempts | ratio | s |
|---|---|---|---|---|
| `CReal.sinFn` | 2,426 | 291,261 | **120:1** | 11.13 |
| `CReal.sinFnUniformConverges` | 3,874 | 300,129 | **77:1** | 11.51 |
| `CReal.sinDominant16Over25CauchyBody` | 6,742 | 267,724 | **40:1** | 10.39 |
| `CReal.cosFnWide` | 2,386 | 119,771 | **50:1** | 4.65 |
| `CReal.weierstrassMTest` | 63,723 | 161,262 | 2.5:1 | 7.64 |
| `CReal.sinFnLowerBoundOneToR` | 14,421 | 36,834 | 2.6:1 | 1.49 |
| `CReal.hasDerivative_unique` | 6,945 | 10,969 | 1.6:1 | 0.52 |
| `CReal.integral_split` | 3,515 | 10,683 | 3.0:1 | 0.58 |

A healthy declaration sits at **1.6–3:1**. The regressed ones sit at
**40–120:1** — the reducer reaches a `Const` head a hundred times for every one
that actually unfolds. **Almost nothing is being delta-unfolded.** Broken down
by name, 98% of `CReal.sinFn`'s attempts are `Nat.succ` (190,806) and `Nat`
(95,345): whnf traversing **unary `Nat` constructor towers that cannot reduce
further**.

Term size does not explain any of it. `CReal.cosWideNonpositive` is 864 nodes
and costs 9.74 s; `CReal.sinFnLowerBoundOneToR` is 8,174 nodes and costs 1.49 s
— a 9.5x size difference in the *opposite* direction, ~60x apart in cost per
node.

**So this is the documented unary-`Nat` mechanism, not the `Definition` one.**
It is the `CLAUDE.md` entry that ends *"keep formed magnitudes small"* — the pi
rung-2 case that went 587 s → 113 s by choosing a bound whose largest formed
`Nat` was 525 instead of 13,125.

## 4. Two sub-mechanisms, and one of them is cheap to fix

The towers are **not** in the stored terms — the deepest `Nat.succ` chain inside
`CReal.sinFn`'s value is **25**, and `CReal.sinFnLowerBoundOneToR` carries one
of depth **3,000** for 1.49 s. They are formed *during reduction*.

An A/B separates them. Building every `NatOps::num` numeral as `Lit::Nat`
instead of a `succ` tower (the ADR-0614 change, throwaway patch, env-gated):

| declaration | unary | `Lit::Nat` | |
|---|---|---|---|
| `CReal.cosWideNonpositive` | 9.74 s | **0.12 s** | **81x**, attempts 99,984 → 2,268 |
| `CReal.sinFn` | 11.13 s | 11.65 s | unchanged, attempts 291,261 → 291,181 |
| `CReal.cosFnWide` | 4.65 s | 4.84 s | unchanged |
| `CReal.sinDominant16Over25CauchyBody` | 10.39 s | 10.21 s | unchanged |
| **whole build** | **105.51 s** | **93.83 s** | −11% |

* **(A) `cos_sign::declare_cos_wide_nonpositive`, 9.7 s.** Entirely
  source-numeral unary arithmetic; the literal representation removes 98% of it.
* **(B) the `trig_fn` family, ~54 s.** Unaffected by literals. The magnitudes
  are formed by *reduction*: `geom_16_over_25_k_final` builds
  `((25*25)+1)+7 = 633` as `Nat.mul(succ 24, succ 24)` over unary numerals, and
  `cos/sin_dominant_16_over_25_cauchy_body_concrete` scales it to
  `k_g = ka*633 + ka*2` with `ka = CReal.bound(two) + 1` — a **concrete** `K`
  threaded through the whole M-test application, so every whnf that touches it
  re-derives the tower. This is the *concrete-witness* hazard `CLAUDE.md`
  documents for `declare_e_converges`, arriving as a magnitude rather than a
  stuck term. **Diagnosed, not fixed** — the fix is a proof change inside
  `trig_fn.rs`, which is another lane's file and real work.

**ADR-0614's "measured at zero" is now stale and should be re-read, not
re-quoted.** It measured 14.91 → 14.23 s (4.6%, noise) *before these three files
landed*. Today the same change is **−11% overall and 81x on one declaration**.
That is still not a reason to adopt it globally — the local fix to
`cosWideNonpositive` gets the same 9.6 s for none of ADR-0614's cost — but the
number in the ADR no longer describes this tree.

## 5. Is the framing wrong? Partly.

- **"Plausibly cumulative and ordinary over 370 commits" — refuted.** Ordinary
  growth accounts for 12.60 → ~22 s. Three files account for the other ~79 s.
- **"Not getting back to 12 s" — right, and the honest floor is higher than it
  looks.** Some of the ~54 s in (B) is genuinely bought: the `16/25` geometric
  modulus is `25² + 8` *because* the ratio is `16/25`, and a concrete
  Weierstrass M-test witness has to name it. What is *not* bought is re-deriving
  that magnitude in unary on every whnf.
- **"The `Definition`-unfold mechanism is the first thing to check" — checked,
  and it is not implicated.** δ-unfold counts on the hot declarations are 2.4k
  against 291k attempts.

## 6. The band, replaced with something that can go red

`scripts/check-creal-prelude-build-ratio.sh` +
`artifacts/creal-prelude-build-budget.tsv` +
`scripts/tests/test-creal-prelude-build-ratio.sh`.

**A seconds budget is not sound here and the ratio is.** Measured on s4, same
binary, same commit, one busy core pinned beside the test:

| condition | `rat_prelude_builds` | `creal_prelude_builds` | ratio |
|---|---|---|---|
| idle (load ~1), run A | 5.22 s | 105.51 s | **20.21** |
| idle (load ~0.3), run B | 5.19 s | 104.61 s | **20.16** |
| one competing core | 10.44 s | 210.57 s | **20.17** |
| `77b71bf10`, idle | 4.85 s | 12.60 s | **2.60** |

Absolute time moves **2.02x** under contention; the ratio moves **0.25%** across
all three HEAD readings. The regression moves it **7.8x**. Both tests are
single-threaded kernel type-checking in the *same binary*, so contention scales
them together and divides out — which is why a seconds gate on this 16-core box
shared by a dozen lanes would spend its life crying wolf, and this one does not
have to be loose to be quiet.

Pinned at **21** (the measured 20.21 rounded up to the next whole unit, ~4%
headroom, ≈20x the observed load sensitivity). `--check` re-demonstrates on
every run that it can fail: it re-runs its own verdict against a halved budget
and fails if that is not RED, and feeds a zero-test transcript through its own
parser and fails if that is accepted. Green is therefore never vacuous.

Controls: 9 cases, all green, driven by canned transcripts and a private pin
file so the suite costs milliseconds and never mutates a tracked file. Each
guard was deleted from a *copy* and the kill counts recorded in the suite's
`--self-table`; G1 kills three (the self-check shares its parser, which is the
coupling working), G4 kills two (a matched positive/negative pair), the rest
kill exactly one.

End-to-end against the real binary: `subject 104.61s / reference 5.19s = 20.16
(budget 21) … GREEN`.

**Not wired into `just check` / `check.sh` by this lane** — those are shared
append points and four clobbering incidents came from lanes writing them. It
costs ~110 s and belongs beside `check-kernel-stack-envelope.sh`. Recommended,
deliberately not done here.

## What the prelude still guarantees

Unchanged. Nothing in `creal/` was edited: `git status` at the end of this lane
shows only the three new files, and `tc.rs`, `creal.rs` and `nat_prelude/ops.rs`
hash identical to `HEAD`. All instrumentation was throwaway, applied and
reverted inside this worktree.
`every_creal_declaration_is_checked_and_axiom_free` and the axiom-freedom claim
are untouched. `cargo fmt --all --check` clean; no Rust file differs from
`HEAD`, so there is nothing new for clippy to see.

## Next

1. Fix (A): `cos_sign::declare_cos_wide_nonpositive`, 9.7 s → ~0.1 s, by keeping
   the formed `Rat`/`Nat` magnitudes small. Smallest, best-understood win.
2. Fix (B): make the `16/25` M-test modulus a *bound* variable through the
   application and substitute the concrete pair only in the final
   Pi-application — `declare_converges_of_cauchy`'s pattern, the one
   `declare_e_converges` had to be rewritten into. ~54 s at stake.
3. Wire the ratio gate into the aggregate gate.
