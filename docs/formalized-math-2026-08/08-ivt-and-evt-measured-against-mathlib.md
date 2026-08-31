# IVT and EVT measured against Mathlib: the Pareto claim holds for one of them

Audit lane `ivt-evt-pareto`, 2026-08-30. **Nothing here reclassifies a fact.**
No fact file was edited; where a fact overstates itself that is reported, and
the fix belongs to a separate lane.

**Correction, 2026-08-30 (lane `ivt-claim-correction`, see
[ADR-0692](../research/09-decisions/adr-0692-the-dominance-test-has-two-axes-not-a-vote-and-ivt-still-passes-it.md)).**
An adversarial audit
([`2026-08-30-session-audit.md`](../research/11-design-review/2026-08-30-session-audit.md)
§Part 1 item 3) found that §4 below applied its Pareto test inconsistently:
three Mathlib-wins were excused for IVT's "Net" verdict and one comparable
Mathlib-win sank EVT's, with no rule stated for the difference. The charge
against the *presentation* held — no test was written down for a reader to
apply themselves. §4 is rewritten below to state the test explicitly (it was
always in `07-the-cost-model-and-pareto-position.md` §1, just never carried
here) and apply it uniformly. The verdict does **not** change to "mutually
non-dominated": under the test `07-…` actually states — trusted base and
computational content, on a statement we ship, with breadth explicitly
conceded rather than scored — IVT dominates cleanly and EVT remains
ineligible for the claim, for the reason ADR-0675 and ADR-0691 already give.
See ADR-0692 for the full adjudication and a fresh re-derivation against the
post-`CReal.supOn` kernel.

**Second correction, 2026-08-30 (lane `evt-row1-land-and-register`, see
[ADR-0895](../research/09-decisions/adr-0895-evt-row-1-lands-and-two-absence-claims-were-wrong.md)).**
§2's "Row 1 — there is none" and ADR-0692's kernel re-derivation both searched
for a declaration named `CReal.supOn_upper_bound` and correctly found it
absent — but that name never existed. The theorem shipped as `CReal.supOn_ub`,
already present in `crates/axeyum-lean-kernel/src/creal/sup_laws.rs` at the
time both documents were written, together with `CReal.supOn_approx_lub`
(the least-upper-bound half). **EVT's row 1 was not missing from the kernel;
it was missing from the ledger and misnamed in the search.** ADR-0895's lane
composed the two into `CReal.evt_approx_max` — the honest row 1, `∀ n, ∃ x ∈
[a,b], ∀ y ∈ [a,b], F y ≤ F x + 1/(n+1)` — and registered all four
declarations (`CReal.supOn`, `CReal.supOn_ub`, `CReal.supOn_approx_lub`,
`CReal.evt_approx_max`) as facts; zero facts had named any of them before.
This does **not** flip EVT's dominance verdict to "dominates" — see ADR-0895's
"What this does NOT change" section — it makes the comparison against
Mathlib's `IsCompact.exists_isMaxOn` newly RUNNABLE, where before there was
nothing on our side to run it against. §2 below is left as the audit wrote
it, since it was an accurate account of the ledger and of a mis-aimed name
search at the time; read it with this note in mind, not as current.

## Summary

The standing goal is: *confirm that the architecture makes results like IVT and
EVT Pareto-dominant over a traditional Mathlib formalization.* Measured against
the kernel environment and against Mathlib at the pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, the honest answer is **mixed, and
different for the two theorems**:

| | IVT | EVT |
| --- | --- | --- |
| ADR-0603 row 1 — general constructive form | **present** (`CReal.ivt_approx`) | **present as of 2026-08-30** (`CReal.evt_approx_max`, ADR-0895 — was reported ABSENT here and in ADR-0692, both searching for a name, `CReal.supOn_upper_bound`, that never existed) |
| row 2 — boundary refutation | **present**, with hypothesis class proved and a discriminating non-vacuity check | **present**, hypothesis class proved, **but no non-vacuity evidence in the ledger** |
| row 3 — decidable-fragment exact form | present, and the substantive half is `cas-internal` | present, and the substantive half is `cas-internal` |
| row 4 — labeled import | **ABSENT** | **ABSENT** |

**IVT is defensibly Pareto-positioned. EVT is not, and the reason is
structural rather than cosmetic: EVT has a refutation of the classical
statement with nothing constructive standing in its place.** The repository
already knows this and says so — `crates/axeyum-lean-kernel/src/creal/supremum.rs`
states in its module documentation that `CReal.supOn` is "still not landed" —
but no fact, and no line of `07-the-cost-model-and-pareto-position.md`, records
that EVT's row 1 is missing while EVT is being cited as a dominance example.

## Method, and a correction to the survey this lane was given

The brief supplied a survey of "15 IVT/EVT facts, all `proved`: 11 `kernel-lean`
constructive rows, 2 that look like row 2, and 4 `cas-certificate` rows," and
asked that it be verified rather than inherited. It does not hold up in three
ways.

1. **The arithmetic is inconsistent.** 11 + 2 + 4 = 17, not 15. The two row-2
   facts are *inside* the 11, not additional to them. The correct split of the
   15 is **9 constructive `CReal` rows + 2 row-2 `CReal` rows + 4 CAS rows**.
2. **The id-substring match under-counts.** Searching fact *contents* rather
   than ids surfaces `F:creal-crossingIndex`, `F:creal-crossingUpper`,
   `F:creal-crossingLower`, `F:creal-crossingClose`,
   `F:creal-crossingCloseClamped`, `F:creal-crossingSampleGeA`,
   `F:creal-crossingSampleLower`, `F:creal-crossingSampleUpper` — the
   Archimedean crossing machinery — and `F:cas-extremum-irrational-argmax` and
   `F:cas-extremum-deriv-sign-bracket-kernel-checked`, which are the *EVT* CAS
   rows and carry neither `evt` nor `extreme` in a form the id match catches.
   `F:cas-extremum-irrational-argmax` is the single most EVT-shaped fact in the
   ledger and the survey missed it.
3. **It over-counts in the other direction.** A content match on `ivt|evt`
   also catches `F:nat-land-assoc` and `F:nat-lor-assoc` (substring hits inside
   unrelated prose), so neither query is a survey on its own.

Everything below is read from the kernel environment or from Mathlib's source.
Fact prose was deliberately *not* used: **9 of the 11 `CReal` IVT/EVT facts
carry `provenance.curation = "generated-unreviewed"`**, and their `statement`
field is boilerplate that says outright it "deliberately makes NO mathematical
characterisation of the theorem." The authority is `formal.statement`, the
rendered kernel type.

Instruments, all run from this lane's own worktree at its own HEAD (a stale
prebuilt binary reports a false ABSENT, which is the one verdict that matters
here):

```
scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel \
  --example prelude_theorem_inventory          # 46.7 s
./target/release/examples/prelude_theorem_inventory --include-constructed
  -> 9,023 rows, distinct: theorems=1948 axiom_free=1948 axiom_bearing=0
```

`prelude_theorem_inventory` lists **theorems, not definitions**, so every
negative below is paired with a positive control of the same declaration kind,
and definition-level questions go through `kernel_declaration_projection`
instead.

## 1. IVT, row by row

### Row 1 — `CReal.ivt_approx`, and it is the real theorem

```text
CReal.ivt_approx : ∀ (F : CReal → CReal) (a b : CReal),
  UniformlyContinuousOn F a b →
  le a b → le (F a) zero → le zero (F b) →
  ∀ (n : Nat),
    ∃ x, le a x ∧ le x b ∧ le (abs (F x)) (ofRat (1 / (n+1)))
```

This is the constructive approximate IVT and it is not a special case dressed
up as a general one: `F` is an arbitrary function with an arbitrary uniform
continuity witness, `a` and `b` are arbitrary, and `n` is universally
quantified, so the conclusion is "roots to any requested accuracy". Axiom
footprint `0`, read from the kernel.

Three real restrictions relative to Mathlib's statement, and it matters that
two of them are *cheap* and one is not:

- **Target is fixed at `0`.** Mathlib's conclusion is `Icc (f a) (f b) ⊆ f ''
  Icc a b` — every intermediate value, not just a root. Ours has a general
  target only in `CReal.ivt_exact_root_at`, which carries the derivative
  hypothesis (below). **Reachable**: `CReal.uniformly_continuous_sub` and
  `CReal.uniformly_continuous_const` are both in the environment, so
  `fun x => F x - t` is a legal instantiation. So this is a gap in what is
  *stated*, not in what is *provable*. It is not currently a fact.
- **One orientation only** (`F a ≤ 0 ≤ F b`). Mathlib carries
  `intermediate_value_Icc'` for the reverse. Reachable via
  `CReal.uniformly_continuous_neg`; also not a fact.
- **Uniform continuity, not pointwise continuity.** This one is *not* cheap,
  and it is not even stateable here — see §3.

### Rows 1b — the bisection family is machinery, not additional statements

`ivt_step`, `ivt_iter`, `ivt_bisect_invariant`, `ivt_bisect_approx`,
`ivt_bisect_cauchy`, `ivt_bisect_cauchy_bound`, `ivt_exact_root`,
`ivt_exact_root_at` are the construction route and its convergence analysis.
Each is a `proved`, axiom-free fact, and each is genuine — but they are not
eight independent IVT statements and should not be counted as breadth.

`CReal.ivt_exact_root` deserves an explicit note because its name invites a
misreading:

```text
CReal.ivt_exact_root : ∀ F F' a b,
  HasDerivativeOn F F' a b → UniformlyContinuousOn F a b →
  le a b → le (F a) zero → le zero (F b) →
  ∀ (n : Nat),
    (∀ x, le a x → le x b → le (ofRat (1/(n+1))) (F' x)) →
    ∃ x, le a x ∧ le x b ∧ Equiv (F x) zero
```

It does produce an **exact** root — but only under a *uniformly positive
derivative* on the whole interval. That is a strictly stronger hypothesis than
Mathlib's `ContinuousOn`, and it is the standard constructive price. Nothing
overstates this; `creal/ivt_boundary.rs` says explicitly that `ivtPlateau` "is
exactly the shape that hypothesis excludes." Counting `ivt_exact_root` as
"we have exact IVT" would be wrong, and no fact does.

### Row 2 — `CReal.ivt_exact_root_decides_sign` survives the harshest reading

```text
CReal.ivt_exact_root_decides_sign : ∀ (v c : CReal),
  le zero c → le c one →
  Equiv (min c (max (add c (neg one)) v)) zero →
  Or (le v zero) (le zero v)
```

Read: *an exact root, in `[0,1]`, of the plateau family
`f_v(x) = min x (max (x−1) v)` decides the sign of `v`.* The conclusion is
analytic LLPO. This is a genuine boundary result, on four counts I checked
rather than took on trust:

- **The hypothesis class is proved, not assumed.** All three of classical
  IVT's obligations are kernel theorems on this very family:
  `CReal.ivtPlateau_nonpos_at_zero`, `CReal.ivtPlateau_nonneg_at_one`,
  `CReal.ivtPlateau_uniformly_continuous`, each axiom-free in the inventory.
  So the family provably lies inside IVT's hypothesis class; the reduction is
  not from a function IVT would decline.
- **The written-out root hypothesis really is the family.**
  `creal_tests::ivt_plateau_is_the_clamp_the_row_two_theorem_uses` pins
  `ivtPlateau v x` definitionally equal to the clamp the theorem states.
- **Non-vacuity is checked, discriminatingly.**
  `creal_tests::ivt_row_two_derives_a_principle_absent_from_the_environment`
  reads `kernel.environment()`, asserts `CReal.le_total`, `CReal.lt_total`,
  `CReal.leTotal`, `CReal.ltTotal` are all absent, and — correctly — pairs that
  with a **positive control of the same declaration kind**, `CReal.lt_cotrans`,
  found by the identical lookup. It also notes that the namespace filter must
  be exact because `Rat.le_total` and `Nat.le_total` both exist. This is the
  rare case of a guard built the way this repository says guards should be
  built.
- **The scope is stated honestly in the source.** `creal/ivt_boundary.rs`'s
  module doc says, without prompting: *"This is **not** a proof that
  `∀ v, Or (le v zero) (le zero v)` is FALSE… ADR-0603 calls this row
  'boundary refutation'; that name is looser than what is proved."*

**The one place it is weaker than its billing.** What is machine-checked is
*absence from the environment under four hand-written names*, not
unprovability. Unprovability of analytic LLPO over this prelude is a
metatheoretic claim and is not checked anywhere. The absence list is a literal,
which is exactly the shape CLAUDE.md warns about: someone landing the same
principle as `CReal.le_or_le` or `CReal.sign_cases` would not trip the guard.
The fact records this evidence under `evidence.kind = "exhaustive-enumeration"`,
which reads stronger than four names. That is the audit's one substantive
criticism of IVT row 2, and it is a criticism of the *label*, not of the
theorem.

### Row 3 — the CAS rows state less than their names suggest

Four CAS facts touch IVT. They split cleanly into two kinds, and the split is
the finding:

| fact | what the kernel actually accepts | `cas_substance.shape` |
| --- | --- | --- |
| `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` | `p(1) < 0` and `p(2) > 0` for `p = x³−2` | `evaluation` |
| `F:cas-ivt-degree4-sign-bracket-kernel-checked-cost-curve` | `p(1) < 0` and `p(2) > 0` for `p = x⁴−2` | `evaluation` |
| `F:cas-ivt-cbrt2-in-1-2` | *nothing* — `cas-internal` | (no block) |
| `F:cas-extremum-irrational-argmax` (EVT) | *nothing* — `cas-internal` | (no block) |

`scripts/check-cas-substance.py` exits 0 with `OK: 14 kernel-reconstructed
cas-certificate fact(s) carry a checked cas_substance block`. **None of the
IVT/EVT/MVT rows is in the `refl` class** — the one refl-shaped row the brief
mentions is elsewhere. So on the substance gate's own axis these rows are clean.

But `evaluation` is the correct and deflating classification. The
kernel-reconstructed IVT rows prove **two rational polynomial evaluations and
their signs**. They do not state IVT. The facts say so themselves, in an axiom
entry that is worth quoting because it is the honest part:

> `cas.ivt-implication-itself-not-reconstructed`: a sign change of `p'` on
> `(-2,-1)` implies, by the intermediate value theorem, that `p'` has a root
> … but that IMPLICATION step is not admitted through this kernel, only the
> two inequalities it would need.

Meanwhile the fact that *does* state the interesting thing —
`F:cas-ivt-cbrt2-in-1-2`, asserting a **unique** root of `x³−2` in `(1,2)` —
carries three CAS axioms including `cas.ivt-certificate-not-kernel-reconstructed`.
So row 3's substance is `cas-internal`, exactly as ADR-0601 requires it be
labeled, and exactly as it must therefore *not* be counted as kernel-anchored
dominance.

One further caveat on the substance gate itself: for all of these rows the
`cas_substance.shape` is **self-reported**, with a recorded
`derivation_declined_reason` saying `scripts/cas_substance.py` has no
certificate artifact to derive from. The gate checks the block's validity, not
the shape's truth.

### Row 4 — absent

Zero facts in the ledger mention `intermediate_value` or `exists_isMaxOn`. Five
facts carry `proof_route = "imported-kernel-lean"`; none is analytic.

## 2. EVT, row by row — and the missing row

### Row 1 — there is none (STALE as of 2026-08-30; see ADR-0895)

**This section's finding was already false when it was written.** `CReal.supOn_ub`
and `CReal.supOn_approx_lub` existed under those exact names at the time; the
probe below searched for `CReal.supOn_upper_bound`, which never existed, and
correctly reported IT absent. `CReal.evt_approx_max` (ADR-0895) is now the
constructive substitute this section says is missing — the composition of
those two theorems through `CReal.le_trans`. What follows is kept verbatim as
an accurate record of the ledger and of a mis-aimed name search on the date
this audit ran; do not read it as the current state.

This is the audit's main finding. Filtering the fresh inventory to
`prelude = creal`, the complete set of `evt`-named theorems is **two**:

```
creal	CReal.evtLinear_uniformly_continuous	0
creal	CReal.evt_attained_max_decides_sign	0
```

and the inventory shard `creal/inventory/extreme_value.rs` — which
`creal_tests::every_creal_declaration_is_checked_and_axiom_free` verifies
against `kernel.environment()` in both directions — lists exactly three
declarations for the whole extreme-value module: `CReal.evtLinear` (def), the
row-2 theorem, and the continuity witness.

Searching for the constructive substitute under any name, with the positive
control that CLAUDE.md requires:

```
positive control: 24 `creal` theorems whose names contain "max"
                  (le_max_left, maxRange_ub, meshMax_mono, …)
under test:       0 theorems matching sup|attain|argmax|maximum|extreme
                  other than evt_attained_max_decides_sign itself
CReal.supOn:      not in the environment
```

The definition-level probe (`scratch-probe.sh`) ran four positive controls —
`CReal.UniformlyContinuousOn` (inductive), `CReal.lt_cotrans` (theorem),
`CReal.maxRange` (definition), `CReal.ivt_approx` (theorem) — all found, and
nine names under test, all reported absent by name:
`CReal.ContinuousOn`, `CReal.Continuous`, `CReal.supOn`, `CReal.sup`,
`CReal.le_total`, `CReal.lt_total`, `CReal.ivt_approx_at`,
`CReal.evt_approx_max`, `CReal.evtSupOn`. The tool's exit status is itself
discriminating, checked both ways:

```
kernel_declaration_projection --require-declaration CReal.supOn      -> 1
kernel_declaration_projection --require-declaration CReal.ivt_approx -> 0
```

And `creal/supremum.rs` states it in its own module documentation:

> **Still not landed: `CReal.supOn` itself**, and therefore none of
> deliverables (a)/(b)/(c) the assignment names in fully assembled form. This
> is not a hedge — it is the honest outcome of a real attempt at the full
> route.

That file is the right place to look for how far it got: `CReal.maxRange` and
its order lemmas, `CReal.meshLevelCount`, `CReal.meshMax` with
`meshMax_step_le`/`_mono`, `CReal.expOfModulus`/`trueExpOfModulus` — five rungs
of the ladder, all axiom-free, none of them the statement.

The same file draws the distinction that makes this a *structural* gap rather
than a bookkeeping one, and it is correct:

> **The supremum VALUE of a uniformly continuous `F` on `[a,b]` is
> constructive. The ARGMAX is not, and never will be with the tools this
> kernel has.**

So EVT's classical conclusion (an *attaining* maximiser) is refuted by row 2 and
is genuinely unavailable; the constructive substitute is the supremum *value*,
and that is the row that is missing. **EVT currently consists of a refutation
with no positive content behind it.**

### Row 2 — the theorem is sound; the ledger evidence is thinner than IVT's

```text
CReal.evt_attained_max_decides_sign : ∀ (v c : CReal),
  le zero c → le c one →
  (∀ t, le zero t → le t one → le (mul t v) (mul c v)) →
  Or (le v zero) (le zero v)
```

Read: *a maximiser on `[0,1]` for the linear family `t ↦ t·v` decides the sign
of `v`.* Mathematically this is exactly as strong as IVT's row 2 — the
conclusion is the *same proposition*, analytic LLPO — and the hypothesis class
is proved rather than assumed, via `CReal.evtLinear_uniformly_continuous`.
`creal_tests` additionally carries two hypothesis-satisfiability tests
(`evt_attained_max_hypothesis_is_satisfiable_at_v_one_c_one` and
`…_at_v_zero_c_zero`), which guard against the maximality hypothesis being
vacuously unsatisfiable — a guard IVT's row 2 does not have and should.

Two asymmetries against IVT, both in the ledger rather than in the kernel:

- **`F:creal-evt-attained-max-decides-sign` carries no non-vacuity evidence.**
  Its two `evidence` entries are "the theorem is in the dependency inventory"
  and "the `creal` prelude is axiom-free." The absence check that makes the
  reduction meaningful lives only in IVT's fact. Since the two theorems have
  the *same* conclusion, the check does cover both mathematically — but an
  auditor reading the EVT fact alone sees a reduction with no evidence that
  its target is unavailable, which is the "reduction to something the kernel
  already proves is worth nothing" failure the IVT test was written to prevent.
- **The fact is `provenance.curation = "generated-unreviewed"` with
  `external_status` absent**, whereas IVT's row 2 is curated with
  `external_status = "proved"`. Nothing in the ledger identifies it as a row-2
  fact at all. The brief's description of it as "looks like row 2" was correct
  precisely because the ledger does not say so.

Also worth recording: `CReal.ivtPlateau_nonpos_at_zero`, `_nonneg_at_one`,
`_uniformly_continuous` and `CReal.evtLinear_uniformly_continuous` — the four
theorems that establish both row-2 hypothesis classes — **have no facts of
their own**. They appear in the ledger only inside one `checker_command` string
in `F:creal-ivt-exact-root-decides-sign`.

### Row 3 — same shape as IVT's, same deflation

`F:cas-evt-endpoint-exclusion-cubic-kernel-checked` kernel-reconstructs
`p(−1) > p(−3)` and `p(−1) > p(2)` for `p = x³−6x`: three evaluations and two
comparisons, `cas_substance.shape = "evaluation"`.
`F:cas-extremum-deriv-sign-bracket-kernel-checked` reconstructs
`p'(−2) > 0` and `p'(−1) < 0`, and states in its own axiom list that it "does
not reconstruct differentiation as a general kernel operation… `cert.deriv` is
taken as given and merely translated."

The substantive EVT statement — `F:cas-extremum-irrational-argmax`, asserting
`∃c ∈ [−3,2]` maximising `x³−6x` with the certificate naming `c = −√2`
exactly — carries four CAS axioms including
`cas.extremum-certificate-not-kernel-reconstructed`. `cas-internal`.

Note the interesting tension, which nobody appears to have written down: the
CAS row asserts an **attained** argmax over the reals, while `creal` row 2
proves that attainment decides the sign of an arbitrary real. There is no
contradiction — the CAS row is over the *real-algebraic* fragment where
sign-deciding is computable by Sturm counting, which is precisely what makes
ADR-0603's row 3 "decidable-fragment exact form" the right name for it. But
the two rows are stating opposite-looking things about EVT and neither fact
cross-references the other.

### Row 4 — absent.

## 3. What Mathlib actually says at `c5ea0035…`

Read from the checkout at `/data0/axeyum/lean-import-toolchain/mathlib4`,
verified at `git log -1` = `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

**IVT** — `Mathlib/Topology/Order/IntermediateValue.lean:552`, under the
variable blocks at lines 223 / 232 / 361 / 548:

```lean
variable {α : Type u} [TopologicalSpace α]
variable [ConditionallyCompleteLinearOrder α] [OrderTopology α]
variable [DenselyOrdered α] {a b : α}
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]

/-- **Intermediate Value Theorem** for continuous functions on closed intervals,
case `f a ≤ t ≤ f b`. -/
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Icc (f a) (f b) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf
```

Three things about it that the comparison has to respect. The domain is **not**
ℝ — it is any conditionally complete densely ordered linear order with the order
topology. The codomain is **any** linear order with an order-closed topology.
And the proof is one line, because it is a corollary of `IsPreconnected`: the
work lives in the topology library, not in the theorem.

**EVT** — `Mathlib/Topology/Order/Compact.lean:246`, under the variable block at
line 143:

```lean
variable {α β γ : Type*} [LinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

/-- The **extreme value theorem**: a continuous function realizes its maximum
on a compact set. -/
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x :=
  IsCompact.exists_isMinOn (α := αᵒᵈ) hs ne_s hf
```

`IsMaxOn f s x` unfolds (`Mathlib/Order/Filter/Extr.lean:113`) to
`∀ y ∈ s, f y ≤ f x`. So Mathlib's EVT is over an **arbitrary compact subset of
an arbitrary topological space**, with codomain any linear order with
`ClosedIciTopology` — not intervals in ℝ. It is derived from `exists_isMinOn`
by order duality, which is again one line over a general library.

**The continuity-notion gap, and why it is not stateable here.** Mathlib's
hypothesis is `ContinuousOn`; ours is `UniformlyContinuousOn` with an explicit
modulus. Classically these agree on a compact interval by Heine–Cantor;
constructively `UniformlyContinuousOn` is strictly stronger, and Bishop takes it
as *the* definition on compact intervals for that reason. Probing the
environment:

```
positive control  CReal.UniformlyContinuousOn -> found  creal  inductive  0
under test        CReal.ContinuousOn          -> "no declaration named
                                                 CReal.ContinuousOn exists in
                                                 any constructed prelude's
                                                 environment"
```

There is no pointwise-continuity predicate in this kernel at all. So the
hypothesis gap cannot even be *stated* here, let alone bridged — which means it
is not a defect to be fixed but a boundary of the formalization. It should be
named in any comparison rather than elided.

## 4. The axes, with evidence

**Revised 2026-08-30 (ADR-0692) — the test, stated once, before either table.**
`07-the-cost-model-and-pareto-position.md` §1 does not claim dominance over an
open-ended axis list. It claims exactly two things, quoted rather than
paraphrased:

> "**On every statement we ship, strictly dominate**: constructive ⟹
> classical plus a program; trusted base 0 vs 3 axioms; every theorem
> executable where Mathlib's analysis is `noncomputable`."
>
> "**Concede breadth EXPLICITLY** at current efficiency … excluded from every
> headline count as a stated invariant."

So a per-statement dominance verdict is decided by exactly **two axes** —
**trusted base** (axiom footprint) and **computational content**
(constructive-with-an-extractable-program vs classical-existence) — measured
on a statement we actually ship that is comparable in content to Mathlib's.
Every other axis below (exactness of the conclusion where it is not already
priced into computational content, generality of the statement, generality
of the ambient structure, which continuity notion is assumed) is **conceded
breadth**: reported for honesty, informative to a reader who needs the fuller
picture, and never scored toward or against the dominance verdict. This is
the rule the original version of this section built two seven-row tables
without ever writing down, which is what let the "Net" lines apply it
differently to the two theorems. Applying the same rule to both:

### IVT

**Dominance axes** (the only two that decide the verdict):

| axis | verdict | evidence |
| --- | --- | --- |
| Trusted base | **we dominate** | `ivt_approx` and all 12 IVT-family theorems read `axiom_footprint = 0` from the kernel. Mathlib's IVT sits on `Classical.choice`, `propext`, `Quot.sound` via the topology library. Uncontested. |
| Computational content (incl. exact vs approximate) | **we dominate** | `ivt_bisect_hi`/`_lo` are definitions the kernel reduces; `ivt_bisect_approx` bounds the accuracy of a *named* algorithm. Mathlib's is a subset inclusion via `IsPreconnected` and extracts no algorithm. The exact-vs-approximate root is the *same trade* read from the other side, not a second axis: Mathlib's root is exact because it assumes classical choice and computes nothing; ours is approximate because it refuses that assumption and delivers a program instead. `07-…`'s own "constructive ⟹ classical plus a program" already prices this as one trade. **This trade is real and permanent** — row 2 (below) is the proof that it is not fixable — and it is exactly what the dominance claim is about, not a loss against it. |

**Conceded breadth** (reported, not scored):

| axis | verdict | evidence |
| --- | --- | --- |
| Boundary statement (row 2) | **we have one; Mathlib has no counterpart** | `ivt_exact_root_decides_sign`, hypothesis class proved, non-vacuity checked with a positive control. A classical library cannot state this — LLPO is a theorem there. Not part of the two-axis test; recorded because it is the strongest thing either library says about *why* the trade above is forced. |
| Generality of statement (target value, orientation) | **Mathlib is more general, reachably** | Ours fixes target `0` and one orientation; `uniformly_continuous_sub`/`_const`/`_neg` are all present, so the general form is an instantiation nobody has landed as a fact. Cheap; conceded per `07-…` §1. |
| Generality of structure | **Mathlib is more general, not reachable here** | Mathlib: any conditionally complete densely ordered linear order → any linear order with order-closed topology. Ours: `CReal → CReal`. This kernel has no typeclasses, no `Set`, no topology. A downstream user who needs IVT for another order gets it there and not here. Conceded, not scored — but genuinely not reachable, unlike the row above. |
| Continuity hypothesis | **not comparable** | `ContinuousOn` does not exist in this kernel; the two statements are not comparable on this axis at all. |

**Net for IVT: the two-axis test holds, for `ivt_approx`.** Trusted base and
computational content both dominate, with no excusing required — the one row
that looked like a third, independent Mathlib-win (exact conclusion) is the
computational-content trade counted twice. Breadth (target, orientation,
ambient structure) is explicitly conceded per `07-…` §1, not scored either
way. The honest, precise claim is *"`CReal.ivt_approx` dominates Mathlib's
IVT on trusted base and computational content; it is narrower in what it
states, by design and by kernel limitation, and that narrowing is reported
above rather than hidden."* — not the unqualified "IVT is Pareto-dominant
over Mathlib."

### EVT

**Dominance axes:**

| axis | verdict | evidence |
| --- | --- | --- |
| Trusted base | **not applicable — no comparable statement exists** | `evtLinear_uniformly_continuous` and `evt_attained_max_decides_sign` are `axiom_footprint = 0`, but neither is comparable content to Mathlib's `exists_isMaxOn`: one is a continuity lemma, the other is an impossibility result. There is no positive EVT statement on our side to compare trusted bases with Mathlib's. |
| Computational content | **not applicable — nothing to compare** | `meshMax` computes a finite mesh maximum and, as of `CReal.supOn` (ADR-0691), a value the mesh maxima converge to — but no landed law connects it to being a supremum, so there is no computed *maximum-realizing* content to set against Mathlib's (non-computable) one. |

**Conceded breadth / other findings** (reported, not scored — because the
dominance axes above are already inapplicable, nothing here could restore or
sink the verdict):

| axis | verdict | evidence |
| --- | --- | --- |
| Boundary statement (row 2) | **we have one; Mathlib has no counterpart** | `evt_attained_max_decides_sign`. The theorem is genuine; the *ledger evidence* for its non-vacuity is missing (§2). Same status as IVT's boundary row: informative, not part of the two-axis test. |
| Generality of structure | **Mathlib is more general, not reachable here** | as for IVT, and more so: Mathlib's is over compact subsets of arbitrary topological spaces. |

**Net for EVT: the two-axis test cannot currently be run, so it is not met.**
This is not "we lose the vote" — it is that Mathlib's comparable content
(`IsCompact.exists_isMaxOn`, a positive attained maximum) has no counterpart on
our side to measure trusted base or computational content against.
`CReal.evt_attained_max_decides_sign` is a different *kind* of statement (a
refutation of what the constructive fragment cannot reach), not a weaker
version of Mathlib's theorem, so it cannot stand in for row 1 in the
comparison. `CReal.supOn` (landed 2026-08-30, ADR-0691) is a real step toward
having one — re-checked against the current kernel with
`kernel_declaration_projection`: `CReal.supOn` is present (`axioms=0`) but
`CReal.evt_approx_max` and a `supOn`-upper-bound-shaped declaration are both
absent, confirming ADR-0691's own statement that the two characterizing laws
are still open. **EVT should not be cited as a dominance example until they
land** — the same conclusion ADR-0675 reached by inventory and ADR-0691 by
construction, now reached a third way by the axis test itself.

**STALE as of 2026-08-30 (ADR-0895): both characterizing laws named above
already existed, under `CReal.supOn_ub` rather than the guessed
`supOn_upper_bound`, and `CReal.evt_approx_max` has now landed as their
composition.** The two dominance-axis rows above still read "not applicable"
honestly for a DIFFERENT reason now: `evt_approx_max` is a genuine positive
statement, but an approximate one against Mathlib's exact attained maximum,
so a fresh two-axis pass is needed to say whether that counts as dominance,
narrower-but-comparable, or something else — ADR-0895 does not make that call
and leaves it for whoever next revisits this table.

## 5. What would have to land

For **EVT** to reach the position IVT already holds, in dependency order:

1. **`CReal.supOn`** — the supremum value of a uniformly continuous function on
   `[a,b]`, as `creal/supremum.rs` scopes it. The five rungs below it are
   landed and axiom-free; the file characterises the remaining obstruction.
   **DONE (landed 2026-08-30, ADR-0691; registered as F:creal-supon,
   ADR-0895).**
2. **`CReal.evt_approx_max`** — the honest row 1: `∀ n, ∃ x ∈ [a,b], ∀ y ∈
   [a,b], F y ≤ F x + 1/(n+1)`. This is the exact structural mirror of
   `ivt_approx` and it is what makes row 2 a *boundary* rather than a *hole*:
   row 2 says the `∀n` cannot be pushed inside, row 1 says everything short of
   that is available. **DONE (landed and registered 2026-08-30, ADR-0895 —
   see F:creal-evt-approx-max).**
3. **A fact for `CReal.evtLinear_uniformly_continuous`**, and non-vacuity
   evidence on `F:creal-evt-attained-max-decides-sign` — either its own test or
   an explicit citation of the IVT one, since the conclusion is the same Prop.

For **IVT**, three smaller items, none of them blocking the claim:

4. **Relabel row 2's absence evidence.** `evidence.kind =
   "exhaustive-enumeration"` overstates a check against four hand-written
   names. Either derive the forbidden set from a property (any `CReal`-namespace
   theorem whose conclusion is `Or (le _ zero) (le zero _)` over a free
   variable) or label it for what it is.
5. **Land the general-target and reversed-orientation forms** as facts. Both
   are instantiations of what exists.
6. **Curate the nine `generated-unreviewed` IVT facts.** Their prose says
   nothing, by design; the family is now this repository's flagship worked
   example and its ledger rows do not describe it.

And one item for the cost-model document itself:

7. **`07-the-cost-model-and-pareto-position.md` should not cite EVT as a
   dominance example until item 2 lands.** It is right that global dominance is
   incoherent and that the claim is per-statement; the audit's finding is that
   for *this* statement the per-statement claim is currently false.

## What this audit did not check

- **Unprovability of analytic LLPO over this prelude is not machine-checked**
  anywhere, and cannot be by a kernel that only accepts proofs. Row 2's
  strength is exactly "the classical conclusion implies a principle absent from
  this environment," and that is the strongest formal statement available.
- **Mathlib's axiom footprints were not measured**, only inferred from the fact
  that `intermediate_value_Icc` routes through `IsPreconnected` and
  `exists_isMaxOn` through `exists_isLeast`/`by_contra`. A `#print axioms` run
  would pin it; it needs a Mathlib build, which this lane did not do.
- **`cargo test` was not run.** Per the lane's brief, targeted runs only; the
  three tests cited (`ivt_row_two_derives_a_principle_absent_from_the_environment`,
  `ivt_plateau_is_the_clamp_the_row_two_theorem_uses`,
  `evt_attained_max_hypothesis_is_satisfiable_at_*`) were **read, not
  executed**. Their existence and content are reported; their passing is not.
