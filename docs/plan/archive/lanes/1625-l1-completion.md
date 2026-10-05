# Lane: l1-completion — L¹ as a metric space, and the price of a completion functor

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (partial, sized)`, l1-completion, 2026-09-05).**

**Landed.** `crates/axeyum-lean-kernel/src/intspace/l1.rs`, 19 declarations,
zero axioms (ADR-1625). The L¹ seminorm `IntSpace.l1Dist` is a **total**
function on `IntSpace.Bundled`, its setoid `IntSpace.L1Equiv b₁ b₂ :=
∫|f₁−f₂| ~ 0` is a definition (so `Metric.distSelf` and `Metric.distEquiv` are
both `fun a b h => h`), and `IntSpace.bundledL1` is a `Metric`. Two instances:
`IntSpace.crealIntervalL1 a b hab` (L¹[a,b]) and `IntSpace.crealFiniteL1 m`
(`E|X−Y|` over counting measure), each with an `Eq.refl` probe pinning the
distance to `CReal.integral |F−G|` and `CReal.sumRange |f−g|` respectively.
`build_intspace_prelude` now calls `build_metric_prelude`.

**The design that unblocked it.** ADR-1612 said L¹ needed `|·|`-closure on the
carrier and priced it as record fields. It does not. What the seminorm needs is
ONE binary operation `fdist : carrier → carrier → carrier` behaving like a
pointwise distance, plus four laws that map one-to-one onto four `Metric`
laws — taken as explicit arguments, so the sixteen-field record and its three
instances are untouched. **All six analytic obligations of both instances are
existing lemmas applied verbatim; zero new estimates.** Three of the six are
`Metric.creal`'s own metric laws (`distSelf`, `absSubLe`, `distTriangle`)
applied at a point — W2-1's `Metric` layer paying a second time.

One rule worth carrying: `fdist` is `|a + −b|`, **not** built from the record's
`fscale (neg one)`. Every `Metric.CReal.*` lemma is stated about `abs (a + -b)`;
the `fscale` route needs a `mul (neg one) x ~ neg x` bridge the ℝ prelude does
not have. *Match the shape the existing lemma is stated in, not the shape the
record makes available.*

**Did NOT land: the completion.** L¹ is a metric space and is **not** known to
be complete; `Metric.Complete (crealIntervalL1 …)` is not declared.

**THE DECIDING NUMBER.** Of the 33 declarations in `creal/completeness.rs` (5)
and `creal/convergence.rs` (28), **33 of 33 are stated about `CReal` alone** and
**1 of 33 is reusable** for a generic completion: `CReal.limit`, which is a
total `Definition` whose `RegularSeq` argument is a `Prop` it only consumes, so
it *can* appear inside a `Definition` producing a `CReal`. It has **zero**
algebra lemmas (no `limit_add`, `limit_le`, `limit_nonneg`, `limit_congr`) and
**zero consumers anywhere in the crate** — the development went through
`Converges` + `speedup` instead and left it standing. **`CReal` is not the
completion functor applied to ℚ and cannot be made one**: `Metric.dist` is
`CReal`-valued so a `Metric` on ℚ presupposes ℝ, there is no `Metric.rat`, and
`CReal`'s regularity is stated on *rational samples* `seq (X m) m`, a shape no
general metric carrier has.

**The next task, fully specified.** A generic `Metric.completion M` is a
*parallel* construction, not a generalization — and it is bounded. The carrier
is available today: `Subtype (Nat → M.carrier) (Metric.Regular M)` is `Sort 1`
and `Metric.subspace` already uses `Subtype` at that universe. `dist` is
`CReal.limit (fun n => M.dist (f n) (g n)) …`. The whole cost is four new
lemmas about `CReal.limit`, provable from `CReal.limit_dist` alone:
`limit_congr`, `limit_le`/`limit_nonneg`, `limit_add`, and a `speedup` bridge
(the sequence `n ↦ M.dist (f n) (g n)` is regular at `2/(m+1) + 2/(n+1)`, twice
what `RegularSeq` demands — the factor-of-two overshoot `creal.rs` already
names). None is deep; all four are new. It is worth more than L¹ alone because
it makes every `Metric` in the library completable at once.

**A cost finding worth carrying.** The obvious negative control — perturb the
integrand in the concrete probe `Metric.dist (crealIntervalL1 …) = ∫|F−G|` and
require a refusal — is **pathological**: to refuse `∫F₁ ≡ ∫F₂` the kernel
unfolds `CReal.integral`, and the run was still going after ten minutes
(measured 2026-09-05, killed). The positive direction is fine and is a shipped
declaration. The mutation table is now stated at a **bound `S` and a bound
`fdist`**, where nothing can unfold: correct / swapped integrand / diagonal
integrand / swapped bundles, three refusals against a positive twin, 67 s for
all three tests. The finite instance keeps a concrete table (bound, negation,
argument order) because its integral is a `Nat.rec` over `CReal.sumRange`; the
interval instance is discriminated on its rendered type instead, which must
contain `fun t => CReal.abs (CReal.add (F t) (CReal.neg (G t)))` verbatim.
General form: **the cost of refusing a definitional equation is the cost of the
reduction the kernel attempts, not the size of the difference between the two
sides.** State the mutation where the heads are opaque.

**A checker finding, not a proof finding.** `Metric.bundledL1` was the briefed
name and would have been watched by **nothing**: `metric::`'s inventory test
never builds `IntSpace`, and `intspace::`'s filter is
`shown.starts_with("IntSpace")`. The names are `IntSpace.*` for that reason —
the same "a prefix filter is still a literal" failure that once left seven
declarations unwatched. The filter is what caught all fifteen new names on
their first run.

<!-- plan-section: landed-changes -->

| 2026-09-05 | l1-completion | `intspace/l1.rs`: L¹ is a metric space (`IntSpace.bundledL1`, 19 decls, 0 axioms, 2 instances, 0 new estimates); the completion is sized at four missing `CReal.limit` lemmas and 1 of 33 reusable — ADR-1625 |
