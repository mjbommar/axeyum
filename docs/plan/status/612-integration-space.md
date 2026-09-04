# Lane: integration-space — W3-1, an integration space with measure derived from the integral (ADR-1612)

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, integration-space, 2026-09-04).** W3-1 tested by
building it. **70 declarations** in a new `IntSpace` namespace, every axiom
footprint empty, 14 tests green in 79 s.
[ADR-1612](../../research/09-decisions/adr-1612-the-integral-is-primitive-and-measure-is-derived-predicatively.md),
Proposed.

**The brief's own deciding metric returns a small number, and the ADR says so.**
It asked how many existing `CReal.integral` theorems become instances of a
general statement rather than needing reproof. Partitioning all 63 declarations
in `creal/integral.rs`: **5 became the record's AXIOMS**, **1 was re-derived**
(`integral_witness_independent`, verified by a test that renders both types and
requires them EQUAL), 3 are blocked on two more fields, 14 relate several
integration spaces at once or vary the endpoint, and 40 are Riemann-sum
construction. **1 of 63 — but 1 of 6**, six being the declarations that are
statements about the integral as a linear functional at all. A record whose
axioms are taken from what a development proves cannot then re-derive what it
took.

**What justifies integral-first is the other direction**: three instances
sharing no machinery (`crealInterval` the Riemann integral, `crealFinite`
`CReal.sumRange` over a finite index set, `crealDirac` a probability space with
`total = 1`); five theorems that are NEW on ℝ, the head of them a congruence
`CReal.integral_le` never got; the same five landing on `CReal.sumRange` at zero
marginal cost; and measure defined from the integral with its two bounds proved
generically.

**Predicativity is adopted as a fourth design constraint** beside setoids
(ADR-1595), hypotheses-not-axioms (ADR-1601) and metric-first (ADR-1602). What
was built is a Petrakis–Zeuner *pre-integration space* (arXiv:2207.08684), not a
Bishop–Cheng integration space — reached by the "axioms from what the integral
proves" discipline before the paper was read, so the switching cost was **zero**.

**Three findings for whoever takes W3-1 next.**

1. **L¹ is blocked on `Sigma`, not on measure theory.** The L¹ pseudometric
   would be a `Metric` instance and would reuse all five of `Metric`'s
   completion statements — except `Metric.dist` is total and integrability is
   `Sort 1` data that `Sigma`'s absence forbids bundling into the carrier. That
   is the **third** independent shelf blocked by that one absence (quotients in
   ADR-1595, bundling an integrable set here, now L¹). Reuse of the completion
   CONSTRUCTION is 0/78 regardless: this kernel has no completion functor, so
   `CReal` is the only completion and it is hand-built.
2. **A blocker this lane wrote down was refuted by its own tool.**
   `uniformly_continuous_abs` has no NAME in the 542-entry `CRealPrelude` field
   list, and a draft of the ADR called it the one lemma blocking L¹.
   `shape_search --concl CReal.UniformlyContinuousOn` found
   `uniformly_continuous_max` and `_min` in `creal/ivt_boundary.rs`; `CReal.abs`
   is `max x (neg x)` by definition; the composition is now
   `IntSpace.CReal.uniformly_continuous_abs`. Search for the STEP.
3. **A handle-derived declaration list is still not the authority.**
   `all_declarations` was derived from `IntSpacePrelude` and `RecordNames` and
   still missed `IntSpace.Triv.rec`, an auto-generated recursor —
   `shape_search --ns IntSpace` said 70 against the list's 69. Fixed by
   `every_live_intspace_declaration_is_listed`, which enumerates
   `kernel.environment()`.

**Not landed, and named rather than hidden**: the ADR-0603 boundary refutation
for monotone convergence (needs a pointwise-`Equiv` congruence for
`CReal.Converges`, absent); dominated convergence; `|·|` and negation on the
carrier, which would move the three `integral_abs_le*` theorems from "blocked"
to "instance" and needs `CReal.neg (mul x y) ~ mul (neg x) y`, absent under any
name; and the ℚ↔ℝ probability bridge (`Rat.expectation` is normalised,
`crealFinite`'s integral is not).

**Reviewer 03 should stay "unmoved" until the completion lands**, and the ADR
says so. Reviewer 08 is unblocked now: a finite index set is an integration
space, a point mass is one, and a detachable subset of a finite index set is an
integrable set.

<!-- plan-section: landed-changes -->

| 2026-09-04 | integration-space | `IntSpace` record (16 fields), generic layer, measure layer, convergence graded family, `crealInterval` + `crealFinite` instances — `63c9a000d` |
| 2026-09-04 | integration-space | detachable subsets, counting measure, the Dirac probability space — `9d47af7e4` |
| 2026-09-04 | integration-space | ADR-1612, three facts, `IntSpace.CReal.uniformly_continuous_abs`, `shape_search`/`kernel_declaration_projection`/`validate-facts` taught the `intspace` group |
