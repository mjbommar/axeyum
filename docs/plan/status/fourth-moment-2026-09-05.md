# Lane: fourth-moment — the first Hoeffding-class rate the carrier can state

<!-- plan-section: lane-status -->

**Four-wise uncorrelatedness, the fourth central moment of a sum, and the `1/m²`
tail that follows, all at ℚ and all axiom-free** (`DONE`, fourth-moment,
2026-09-06, ADR-1653).

## What this slice is

ADR-1631 closed the binomial slice with a sized obstruction rather than a gap in
effort: Hoeffding needs `E[∏_j f(X_j)] = ∏_j E[f(X_j)]`, which is about a JOINT
law over a product space, and this development has one weight function over one
index range; and Hoeffding's lemma needs `expFn_add`, which exists on no carrier
here. It named the next rate that IS statable, and this lane is that rate.

The shelf now carries, at ℚ:

* Chebyshev on a sample mean — tail `1/m`;
* **the fourth-moment tail — `1/m²`.**

That gap is the whole return on paying for the fourth moment, and it is the
first Hoeffding-class rate this carrier reaches.

## Partition check

Run before proving anything. `artifacts/structural-index/held-out-exclusion-
manifest.json` holds 136 held-out fact ids, every one of them `F:ml430-int-*`;
`artifacts/autogenesis/nursery-v2-extension.json` names 54 families, all
integer/natural arithmetic and none rational, probabilistic, or
moment-shaped. Coverage confirmed positively (`partition` occurs 579 times in
the nursery file; the family list was read out in full), so the empty result is
a real negative and not a grep that never pointed at its subject. **No target
of this lane is in a blind evaluation population.**

## What landed

Six declarations in one new file, `crates/axeyum-lean-kernel/src/rat_prelude/fourth_moment.rs`:

| name | what it says |
| --- | --- |
| `Rat.expectation_sumVars_mul` | `E[(Σ_{i<m} Y_i)·W] = Σ_{i<m} E[Y_i·W]`, for ARBITRARY `W` and with no hypothesis at all |
| `Rat.expectation_sumVars_mul_eq_zero` | the same with every per-index term known to vanish |
| `Rat.FourwiseUncorrelated` | the `Definition`: lone-index mixed moments vanish, and squares are uncorrelated |
| `Rat.expectation_sq_sumVars_mul_sq` | `E[(Σ_{i<m} Y_i)²·z²] = Σ_{i<m} E[Y_i²·z²]` — the one cross term the fourth power does not kill |
| `Rat.fourth_moment_sumVars_le` | `E[(Σ_{i<m} Y_i)⁴] ≤ Σ_{i<m} M₄ + 3(Σ_{i<m} σ²)²` |
| `Rat.fourth_moment_tailSumVars` | `a⁴·E[𝟙[(Σ − EΣ)⁴ ≥ a⁴]] ≤ Σ_{i<m} M₄ + 3(Σ_{i<m} σ²)²` |

## The four calls worth reading (ADR-1653)

1. **The lone-index condition is ONE universal, not three.** "Some index occurs
   exactly once" is, after a commutative reordering, "the last slot differs from
   the other three", and that single condition covers all three unpaired
   multinomial shapes.
2. **One hypothesis-free peeling lemma carries the whole proof.** `W` being
   arbitrary is load-bearing: in every use it MENTIONS the sum being peeled.
3. **`Rat.sumRange_delta` is unusable here** — its hypothesis is unrestricted
   (`∀ t, t ≠ i → …`) and four-wise uncorrelatedness supplies zeros only below
   the bound. A bounded `sumRange_delta_lt` would be a real addition to
   `rat_prelude/sum.rs`; it was not needed once the diagonal lemma had its own
   induction.
4. **The bound is `sumRange`-shaped and the induction closes with `3σ⁴` of
   slack**, not on the nose. `sumRange f (succ b) ≡ sumRange f b + f b` is
   `Eq.refl` here; `natDivSucc (succ b) 0 = natDivSucc b 0 + 1` is not a fact
   this prelude has.

## Gates, with counts and exit status

| gate | result |
| --- | --- |
| `cargo check -p axeyum-lean-kernel --all-targets` | exit 0, no errors, no warnings |
| `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` | exit 0 after one fix (two `needless_range_loop` errors); zero errors, zero warnings |
| `cargo fmt --all --check` | exit 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- rat_prelude::` | **313 passed, 0 failed**, 2220 filtered out, 1286.86 s. Includes `every_rat_declaration_is_checked_and_axiom_free` (the every-declaration sweep), `every_named_declaration_exists`, and `rat_prelude_is_axiom_free` — all `ok` |
| `cargo test --release … -- rat_prelude::fourth_moment` | 6 passed, 0 failed, 25.86 s |
| `rat_theorem_inventory` on each new name | 5 theorems derived, **5 with an EMPTY axiom footprint**, 0 asserted |
| `validate-facts.py` | exit 0, 2929 facts, 0 errors, `missing_edges=0` |
| `check-settled-fact-statements.py` | `PASS`, `drifted=0`, `header_exempt=0` |
| `check-kernel-trusted-core.py` | exit 0, 5 guards, 0 failures |
| `check-autogenesis-holdout-isolation.py` | `PASS`, `held_out=206`, `settled=0`, `references=0` |
| `check-merge-hygiene.sh` | `PASS` (after regenerating the shape census and provenance ledger) |
| `mutation_controls.py --check-anchors` | no `NOT APPLIED` / `AMBIGUOUS ANCHOR` for this suite |

## Mutation table — every row RUN, none predicted

Suite `fourth-moment-concentration`, baseline green at 6 tests.

| mutation | outcome |
| --- | --- |
| the multinomial coefficient 3 becomes 6 | **killed 6** (the whole suite) |
| the tail threshold `a⁴` becomes `a²` | **killed 6** (the whole suite) |
| the coefficient test's negative control becomes a second copy of its positive case | **killed 1** — exactly `fourth_moment_bound_carries_three_square_terms_and_not_six` |
| the threshold test's negative control becomes a second copy of its positive case | **killed 1** — exactly `fourth_moment_tail_threshold_is_a_to_the_fourth_and_not_a_squared` |

The first two are kernel kills and that is the finding, not a shortcoming: a
wrong constant here is not a wrong theorem the tests have to notice, it is a
term whose inferred type stops matching its declared one, so
`build_rat_prelude` returns `Err` and every registered test dies at
`prelude()`. The last two exist because a negative control fails two ways —
vacuous is as bad as absent — and each kills exactly the one test that owns it,
which is what says the controls are load-bearing rather than decorative.

## The cost, measured and flagged NOT COMPARABLE

The rat prelude got slower. Building it once in `--release` now takes **13.95 s**
on this host under other lanes' load, and the 313-test `rat_prelude::` sweep
took **1286.86 s** at `--test-threads=4` (every one of those tests builds the
prelude). The comparable earlier number from this lane is the `fourth_moment`
filter at **8.68 s** for 4 tests when only the three stage-1 declarations
existed, against **25.86 s** for 6 tests now.

Those two numbers are **not comparable** — different test counts, different
thread rounds, different machine load — and a clean before/after with the
module's `declare_fourth_moment_all` short-circuited **did not run**. What can
be said is that the sixteen-monomial ring expansion and the three nested
peeling applications are the largest proof terms in this prelude and the build
cost is visible. Sizing that properly, and reducing it, is the obvious
follow-up.

## Hoeffding is still blocked, and for the same two reasons

Re-checked, not inherited: no product space (so no joint law to state
`E[∏ f(X_j)] = ∏ E[f(X_j)]` over), and no `expFn_add` on any carrier here.
Nothing in this slice moves either.
