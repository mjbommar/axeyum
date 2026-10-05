# Lane: binomial-hoeffding — Bernoulli and binomial distributions, and a tail bound (W3-12)

<!-- plan-section: lane-status -->

**Lane `binomial-hoeffding` (`DONE`, 2026-09-05).** ADR-1631. Twelve
declarations, all axiom-free.

The **Bernoulli distribution is now constructed**, not assumed:
`AlgS.OrderedRing.bernoulliVar` / `bernoulliMass` over
`(R : AlgS.OrderedRing)`, with `bernoulli_isDistribution` — the first
`IsDistribution` in the repository discharged from a construction rather than
hypothesised — and `E[X] ≃ q`, `Var[X] ≃ q·(1 − q)`. The variance goes through
without `mulComm`: the only commutativity the identity needs is
`(1 − q)·q ≃ q·(1 − q)`, and both sides expand to `q + −(q·q)`. Two generic
ring lemmas the spine lacked (`mul_neg`, `zero_add`) came out of it.

The **binomial's mean and variance are two lines each** over the shelf
ADR-1616 built — `expectation_sumVars`/`variance_sumVars` plus one shared
`sumRange_congr_lt` + `sum_range_const` helper — but they live at `ℚ`, not
over the record, because the variance of a sum needs `variance_eq`, which
needs `mulComm`. That is a measured record boundary: the moment
`AlgS.CommOrderedRing` exists the three theorems move up verbatim. **Next
slice, and it is bounded: add `mulComm` as a record (or as an explicit
hypothesis) and migrate `variance_eq`.**

**Hoeffding did NOT land, and the blocker is not `exp`.** `CReal.expFn`
exists; `CReal.expFn_add` does not, and before either matters Hoeffding needs
`E[∏ f(X_j)] = ∏ E[f(X_j)]` — a joint law over a product space that a
one-weight-function development cannot express. Both absences measured against
a 4,260-declaration `shape_search --include-constructed` index. The reachable
tail bound landed instead: `Rat.fourth_moment_inequality`, Markov at the fourth
power. **Two gates were already red on `main` before this lane's merge base and are
NOT this lane's to regenerate**: `gen-theorem-production-ledger.py --check`
(pinned 2,539 on 2026-09-03, measures 2,829 now — this lane contributes 10 of
the 290) and `gen-ledger-coverage.py --check` (same pin date). Both are
cross-lane shared artifacts; regenerating either here would put a +290
production claim in a lane that produced 10.

**Next slice for a Hoeffding-class rate: `E[(Σ − EΣ)⁴] ≤ 3(mσ²)²` under
4-wise uncorrelatedness — statable here (it is about covariance-like
quantities, not a joint law), and the work is the fourth-power expansion.**

<!-- plan-section: landed-changes -->

| 2026-09-05 | `0e5f3a3ad` | `rat_prelude/binomial_s.rs`: the Bernoulli distribution constructed over `AlgS.OrderedRing` — `bernoulliVar`, `bernoulliMass`, `bernoulliMass_nonneg`, `bernoulli_isDistribution`, `bernoulli_expectation`, `bernoulli_variance`, plus the generic ring lemmas `mul_neg` and `zero_add`. (ADR-1631) |
| 2026-09-05 | `1898e9651` | `binomial_s_tests.rs`: nine tests. `q = 1/2` cannot separate `q(1−q)` from `q·q` (both `1/4`); `q = 1/3` can (`2/9` against `1/9`), and the suite says so in its own assertions. |
| 2026-09-05 | `dd6a0df24` | `rat_prelude/binomial_rat.rs`: `Rat.binomial_expectation`, `Rat.binomial_variance`, `Rat.binomial_chebyshev`, and a suite that discharges the per-trial hypothesis from the GENERIC Bernoulli theorem and then computes: three Bernoulli(1/3) trials have mean `Rat.one`. |
| 2026-09-05 | `04ad1af63` | `Rat.fourth_moment_inequality` — the tail bound reachable without an exponential. Hoeffding's two blockers named and measured. |
| 2026-09-05 | `b8243a54a` | ADR-1631, six facts, the lane status, and the `bernoulli-binomial-model` mutation suite. `validate-facts.py` derived 18 `depends_on` edges from the proof terms that nobody would have written by hand. |
| 2026-09-05 | `197f26e1b` | The remaining four ADR-1631 theorems registered, so all ten are in the ledger; registering `zero_add` and `mul_neg` made three EXISTING entries incomplete and the ledger noticed. |
| 2026-09-05 | `b1c450453`, `f4cb80c35`, `9385cd877` | Generated-artifact and formatting follow-ups: production-provenance ledger, `rustfmt` on the two files the `pub(super)` widening reflowed, private-helper census (`files_scanned` 616 → 620, exactly this lane's four files). |
