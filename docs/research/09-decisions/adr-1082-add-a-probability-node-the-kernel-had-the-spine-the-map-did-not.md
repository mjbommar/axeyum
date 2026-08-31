# ADR-1082: Add a probability node — the kernel had the spine, the map did not

Status: accepted
Date: 2026-08-31
Index-summary: Adds `probability` (layer 3, destinations) to
`docs/curriculum/curriculum.toml` and its `axeyum-scenarios::mathtour` mirror,
on prerequisites `rationals` + `counting` — the two nodes
`crates/axeyum-lean-kernel/src/rat_prelude/probability.rs` actually builds on
(`Rat.sumRange` and its monotonicity, nothing else). Measured against a fresh
`kernel_declaration_projection`: exactly 47 axiom-free `Rat.*` declarations
(8 `Definition`s, 39 `Theorem`s) — `IsDistribution`, `expectation` with
linearity/monotonicity, `variance`/`covariance` with Cauchy-Schwarz
(`covariance_sq_le_variance_mul`), Markov's and Chebyshev's inequalities, and
`weak_law_of_large_numbers` — that had no curriculum node to attribute to
before this ADR and attributed to `rationals` for want of a better bucket.
`status = "planned"`, the first node in the file to use that value: the
content is bounded/computable (an ordinary `QF_LRA` fragment, not a
proof-reconstruction target), but no self-checking `axeyum-scenarios::Family`
exists for it yet, so `Status::Covered`'s test-enforced definition — "has a
self-checking exercise family today" — does not hold. Also re-measures and
corrects five other nodes' `kernel_decls` (`naturals`, `integers`,
`rationals`, `number-theory`, `linear-algebra`), which had drifted from the
figures ADR-1075 pinned hours earlier the same day, purely from other lanes'
commits landing in between — not from this change.
Index-status: accepted

Related: ADR-1075 (the curriculum graph measures scenarios, not the kernel;
adds the `kernel_decls` axis this ADR uses), ADR-0033 (double-duty
educational artifacts), ADR-0512 (`CReal`, for contrast — probability needs
no analysis carrier at all, only `Rat`).

## The finding

`docs/curriculum/curriculum.toml` mentions probability zero times (control:
`linear-algebra` is mentioned 4 times, so the query was aimed correctly).
Meanwhile `crates/axeyum-lean-kernel/src/rat_prelude/probability.rs` is 6,869
lines building a coherent, Spivak-shaped spine entirely over `Rat`:

```
distributions -> expectation -> variance/covariance -> Markov -> Chebyshev -> weak law
```

Measured directly from a fresh `kernel_declaration_projection` (release;
debug SIGABRTs on this build), filtered to the `rat` prelude section and
matched by name — not inferred from source text or a doc comment:

```sh
cargo run --release -p axeyum-lean-kernel --example kernel_declaration_projection \
  | awk -F'\t' '$1=="rat" && $3 ~ /^Rat\.(IsDistribution|expectation|Expectation|variance|Variance|covariance|Covariance|markov|Markov|chebyshev|Chebyshev|weak_law|bernoulli|Bernoulli|uniform|Uniform|indicator|Indicator|prob_|Prob|sumVars|PairwiseUncorrelated)/' \
  | wc -l
```

gives **47**, matching the brief's claim exactly: 8 `Definition`s
(`IsDistribution`, `expectation`, `variance`, `covariance`, `uniform`,
`indicator`, `sumVars`, `PairwiseUncorrelated`) and 39 `Theorem`s, including
`covariance_sq_le_variance_mul` (Cauchy-Schwarz for random variables),
`markov_inequality`, `chebyshev_inequality`, `chebyshev_sampleMean_uncorrelated`,
and `weak_law_of_large_numbers` / `bernoulli_law_of_large_numbers`. All 47
attributed to `rationals` in `scripts/measure-curriculum-kernel-coverage.py`
before this change, simply because no better bucket existed — the same
observation the sibling lane's DEPTH-PROPOSAL document made in passing
(`docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md` S3)
without landing a node for it, deliberately: that document's whole point was
that adding ~30 rung-level nodes to the two existing destinations moves five
consumers and should be a separate reviewed step (ADR-1075), not that
probability itself should stay unmapped forever.

This is the strongest available evidence that the map's blind spot named in
ADR-1075 is structural, not incidental: a destination-sized body of proved,
axiom-free mathematics sat entirely outside the 23-node graph, invisible to
every consumer that reads `curriculum.toml` — the dispatcher, the
foundational-concepts atlas, the import backlog.

## The decision

**Add one node, `probability`, as a layer-3 destination — not a rung-level
spine.** Two reasons, both from the sibling ADR-1075/DEPTH-PROPOSAL work:

- The existing three destinations (`number-theory`, `linear-algebra`,
  `calculus`) are each ONE node standing for dozens to hundreds of kernel
  declarations; a rung-level breakdown is a proposed, not adopted, future
  step for those two, explicitly deferred because it moves five consumers.
  Probability's 47 declarations are the same order of magnitude as
  `linear-algebra`'s 55 (pre-correction) or `number-theory`'s 105 — destination
  scale, not structure scale.
- A small, correct addition beats a large one that breaks consumers. Adding
  a single node keeps the diff to: `curriculum.toml` (one node + two
  `unlocks` edges), the `mathtour.rs` mirror, one markdown page, and one new
  entry each in `scripts/gen-foundational-concepts.py`'s `CURRICULUM_MAP` and
  `scripts/measure-curriculum-kernel-coverage.py`'s `BUCKETS`/`NODES`.

**Prerequisites are `rationals` and `counting`, not `reals` or
`sequences-and-limits`.** Read from what `probability.rs` actually imports
(`super::sum::{bounded_nonneg, bounded_pointwise_le}` for `Rat.sumRange` and
its monotonicity, `super::ops`/`super::group` for plain `Rat` arithmetic, and
`int_prelude::ops::IntDev`/`nat_prelude::NatOps` as the ambient kernel
plumbing every prelude file uses) rather than from how probability is usually
taught. A finite distribution needs no analysis: `ℚ` is enough, and the
module's own doc comment says so explicitly ("A finite probability
distribution needs no analysis — `ℚ` is enough"). This is confirmed by the
two kernel constraints DEPTH-PROPOSAL names as structural: there is no
`List`/`Finset`/`Prod`, so a finite family is a function-plus-bound exactly
as `Rat.sumRange` encodes it, and every statement here is a scalar
(`expectation`, `variance`, a probability, an inequality between rationals),
never an equation between functions, so the `funext`-absence constraint never
bites.

`rationals.unlocks` and `counting.unlocks` both gain `probability`, keeping
the file's own documented invariant (every `unlocks` is the inverse of some
`prerequisites`) intact — checked by
`crates/axeyum-scenarios/src/mathtour.rs`'s `prerequisites_reference_real_nodes`
test family, which passed against all 6 `mathtour::tests::*` after the edit.

**`status = "planned"`, not `covered` or `lean-horizon`.** This is the first
node in the file to use `planned` — every existing node was either `covered`
or `lean-horizon`, even though the enum and the README's own status legend
have always defined three values. The choice is dictated by
`Status`'s own definitions in `crates/axeyum-scenarios/src/mathtour.rs`:

- Not `covered`: `Status::Covered` means "has a self-checking exercise family
  today", enforced by `covered_nodes_have_a_family_realized_by_a_self_checking_scenario`
  against `all_catalog_scenarios()`. No `Family::Probability` variant exists
  and no scenario realizes one, so marking this node `covered` would assert a
  family that does not exist and would fail that test — exactly the mistake
  ADR-1075 rejected for `calculus`.
- Not `lean-horizon`: that value means "primarily a proof-reconstruction
  target, not a benchmark" (undecidable general theorems, non-constructive
  reasoning). Nothing here is that — every declaration is a finite,
  bounded, `QF_LRA`-shaped fact over concrete or symbolic-but-finite
  rationals, the same computable fragment `Rational`'s own `Family` already
  exercises. Calling it Lean-horizon would misdescribe genuinely
  benchmark-shaped content as proof-assistant territory.
- `planned` says exactly the true thing: "testable fragment identified,
  family not yet built." A validated foundational example pack already
  exists for this ground (`artifacts/examples/math/finite-probability-v0`),
  reused as this node's `CURRICULUM_MAP` pack entry; what remains is a
  dedicated `axeyum-scenarios::Family` and scenario generator, sized as
  ordinary future work rather than a blocker.

## What was corrected along the way

Re-running `scripts/measure-curriculum-kernel-coverage.py` against a fresh
projection (mandatory to compute `probability`'s own `kernel_decls`) showed
the total moved from ADR-1075's `2,562` distinct declarations / `2,433`
attributed, measured hours earlier the same day, to **2,586 / 2,454** —
purely from other lanes' commits landing in between (new `Nat.avg`,
`Nat.Pair`, `int_prelude::euler_prod_pow`/`euler_unit_range` declarations,
and a matrix-inverse fact fix), not from this ADR's own change, which is
attribution-neutral for the total (it only moves the 47 probability
declarations out of the `rationals` bucket into their own). Five of the
23 pre-existing nodes' pinned `kernel_decls` had drifted from the fresh
measurement and are corrected here as a direct byproduct of the same
command: `naturals` 505→512, `integers` 185→186, `rationals` 251→211 (the
−47 move plus +7 independent growth), `number-theory` 105→107,
`linear-algebra` 55→59. The other 18 nodes matched exactly and are
untouched. The header comment's worked example and totals are updated to
match, and its own text now says plainly that re-measuring is expected to
move the number — no node beyond these five was re-audited, and a
systematic re-measurement of the whole file remains future work for whoever
owns that axis.

The residual (declarations attributable to no bucket) grew from 129 to 132:
still the 30 legacy `AxReal` axioms and the 94-declaration string package,
plus 8 newly-landed declarations not yet in any bucket (`Nat`/`Int`/`Rat`/
`Complex`/`CPoint` — the carrier inductives themselves — and `Max.max`,
`Min.min`, `Squarefree`, `instMinNat`). Left alone; out of scope for this
change.

`gen-foundational-concepts.py`'s `artifacts/ontology/foundational-concepts.json`
atlas regenerates cleanly to 138 rows (24 curriculum, up from 23) and
`validate-foundational-concepts.py` passes. `artifacts/import-backlog.json`
was regenerated once to confirm this change does not affect it (it did not —
`git diff` against the regenerated file shows zero mentions of
`probability`), then reverted: that file was already stale before this ADR,
from fact-ledger movement independent of the curriculum graph, the same
pre-existing red gate ADR-1075 found and deliberately left alone.

## Consequences

- `docs/curriculum/curriculum.toml` has 24 nodes; `crates/axeyum-scenarios/src/mathtour.rs`'s
  `NODES` mirrors it exactly (verified: all 6 `mathtour::tests::*` pass).
- `scripts/measure-curriculum-kernel-coverage.py` gains a `probability`
  bucket, placed before the generic `rationals` catch-all so the 47 `Rat.*`
  names it claims do not fall back through to `rationals`.
- `scripts/gen-foundational-concepts.py`'s `CURRICULUM_MAP` gains a
  `probability` entry reusing the existing `finite-probability-v0` pack.
- No scenario, dispatcher, or fact-ledger behavior changes: `status =
  "planned"` is excluded from `scripts/check-curriculum-coverage.py`'s
  scenario-coverage table exactly as the existing `lean-horizon` nodes are
  (verified: the script's output and exit status are unchanged by this ADR).
- Building a `Family::Probability` scenario (Markov/Chebyshev instances with
  witness distributions, refuted-by-negation for a bad bound) is now a named,
  dispatchable task rather than invisible work with no home in the graph.
