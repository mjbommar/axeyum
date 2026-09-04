# Lane: metric-compactness — W2-3 Bishop compactness / EVT-as-instance, W2-2 continuity as a metric notion

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, metric-compactness, 2026-09-04).** ADR-1602 bet
that the metric carrier would carry W2-2 and W2-3 "with no further design
decision". This lane built both and the bet holds: **44 declarations, all
axiom-free, 43 of them admitted the first time the kernel saw them**, in
`metric/continuity.rs` (15), `metric/compactness.rs` (19) and
`metric/interval.rs` (10). ADR-1607 records the measurement.

W2-2: continuity over an **arbitrary pair** of metric spaces, uniform and
pointwise, each with a predicate-relativized twin, plus
`Metric.creal_continuous_on` from `CReal.UniformlyContinuousOn`. That bridge
costs **zero estimates** — its witness is `UniformlyContinuousOn.modulus`
verbatim and its proof is that witness's `spec` applied to four `And`
projections, because `uc_spec_body` was already in the `1/(k+1)` shape and
`Metric.dist Metric.creal` reduces to `CReal.abs (x + -y)`. The uniform ⇒
pointwise arrow is one-directional on purpose; the converse is Heine–Cantor
and needs the finite subcover this library declines.

W2-3: Bishop compactness (`TotallyBounded` + `Complete`, no covers), the
Extreme Value Theorem over any **totally bounded** subset of any metric space
— completeness is not used, and a test reads that off the rendered type — and
the closed real interval as an instance: `Metric.creal_compactOn_interval`.

**The instance claim is a measurement, not a reading.**
`Metric.creal_evt_approx_max` (through `CReal.supOn`) and
`Metric.creal_evt_approx_max_via_metric` (through the general metric EVT)
carry the **same interned `ExprId`**, built by separate code in two modules,
with the general EVT's own type in the same test as a non-vacuity control.

**The finding worth carrying forward: the general theorems are cheap and the
INSTANCES are where the work is.** The interval instance needed a clamp
lemma, a grid induction, and one `Rat.natDivSucc` scaling identity — 10
declarations for one carrier, against 34 for every carrier. Size
"prove X generally, then instantiate" with the instantiation weighted at
least as heavily as the theorem.

**A tooling finding.** Three proof terms had `pi_fv` where they needed
`lam_fv`. The kernel calls that `NotASort`, which names nothing, and inside a
seventy-call straight-line `build_metric_prelude` the first symptom was a
ten-minute typecheck growing 1 GB of RSS every 30 s on a shared box.
`declare_all` in both new modules now runs from a `[(label, fn)]` table and,
under `AXEYUM_METRIC_TIMING=1`, prints one line per declaration with its wall
clock and whether the gate accepted it; that located the culprit in one run.
Any straight-line `declare_*` sequence long enough to hide a slow member
should carry the same table.

Gates: `metric::` 29 tests green (was 17) in 88.95 s; clippy `-D warnings`
clean on `-p axeyum-lean-kernel --all-targets --all-features`;
`cargo fmt --all --check` clean; `validate-facts.py` 2,783 facts / 0 errors;
census regenerated. Four new facts, four new negative controls each with a
positive twin in the same test, and two coverage tests that derive their
subject from `Kernel::environment` rather than from a literal.

Not done, and named for whoever picks it up: the Euclidean plane
(`Metric.cpoint`) still has no completeness theorem and no compact subsets;
the general statements are now in place, so that work is entirely in the
instance. The approximate **minimum** is not proved (it would be this EVT
applied to `-F`, but that composition is not in tree).

<!-- plan-section: landed-changes -->

| 2026-09-04 | metric-compactness | lane opened: W2-3 + W2-2 on the `Metric` carrier, ADR-1607 reserved |
| 2026-09-04 | metric-compactness | `metric/continuity.rs` + `metric/compactness.rs`: 34 declarations — continuity over an arbitrary pair of metric spaces, Bishop compactness, and the EVT over a totally bounded subset (`12fed830b`) |
| 2026-09-04 | metric-compactness | `metric/interval.rs`: a closed real interval is Bishop-compact, and the interval EVT is the metric EVT at one interned type (`378e7cecd`) |
| 2026-09-04 | metric-compactness | ADR-1607, four facts, and the lane close-out |
