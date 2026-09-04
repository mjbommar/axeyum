# ADR-1601: classical logic enters as a hypothesis, not as an axiom

Status: proposed
Date: 2026-09-04
Lane: `classical-axiom-policy`
Roadmap: W0-2 (convergence C4 — reviewers 03.1, 12.2) and W1-9 (reviewer 10.1)

Index-summary: two reviewers asked whether classical logic should enter as a
labelled axiom in `Kernel::axiom_footprint` or as an explicit hypothesis
discharged at use. Decided by measurement, not by argument: the
reverse-mathematics map was extended (LPO, WLPO, Markov's principle, LLPO over
ℕ — `nat_prelude/omniscience.rs`, six theorems) **and** four classical
theorems about `CReal` that this development's own field documentation records
as unavailable were stated and proved on an explicit order-decision hypothesis
(`creal/omniscience.rs`) — `le_total`, trichotomy, the Markov direction on
apartness, and the `abs` sign decision. All ten admit with an **empty axiom
footprint**. **The measured cost of the hypothesis route across the ten
theorems is 11 binders, 14 argument positions, and ZERO new obligations** —
the hypothesis is never re-derived, never weakened, and never generates a side
condition, and two of the four `CReal` theorems consume another theorem of the
family, so the number is a *carrying* cost and not a one-statement cost. Three
findings decide it: the axiom option is not one name but **at least three**
(03's own blocker names EM, countable choice *and* `funext`); it would
retroactively devalue the three existing row-2 certificates
(`lub_decides_em`, `ivt_exact_root_decides_sign`,
`evt_attained_max_decides_sign`), whose whole content is that a classical
conclusion *costs* a decision principle; and it kills three environment-scan
gates that currently pass. **Recommendation: option (b), classical principles
stay hypotheses.** Reversible on evidence — a named, attempted theorem shown
unreachable this way.
Index-status: proposed

## Context

Reviewer 03 (classical analysis) is the department's only *unmoved* reviewer,
and its blocker is a decision rather than a construction:

> Classical analysis needs excluded middle, countable choice, and function
> extensionality, and the kernel has none of them. The library's headline
> metric is that its axiom footprint is empty, and importing this reviewer's
> subject means giving that up for the part of the library that serves them.
> […] That choice — classical axioms as footprint entries, versus classical
> hypotheses discharged at use — is this reviewer's real question for the
> project, and it is unresolved.

Reviewer 12 (the chair) makes W0-2 being *written* one of two conditions for
signing the department report. Reviewers 08 (probability) and 10 (logic) are
gated on it indirectly — 10.3's first-order completeness needs a choice
principle, and 08's limit theorems need measure theory, which needs W0-2.

W0-2 and W1-9 are one task, and that is the shape of this ADR. W1-9 asks for
the reverse-mathematics map to be extended beyond the existing
`Nat.em_implies_lnp` / `Nat.lnp_unrestricted_implies_em` equivalence. **The
map is the evidence for the policy**: it shows which classical principles buy
which theorems, and whether carrying them as hypotheses is tolerable in
practice. ADR-1595 settled the sibling question (quotients) by building the
theorem and counting the obligations rather than by weighing arguments. This
ADR does the same.

### What the library already had

Two halves of an argument that had never been put together:

- **The hypothesis route works over ℕ.** `least_number.rs` proves
  `Nat.lnp_unrestricted_implies_em` and its converse `Nat.em_implies_lnp`,
  with excluded middle as an explicit `∀ (P : Prop), Or P (Not P)` binder and
  the footprint empty. Reviewer 10 calls it "real reverse mathematics" and
  "stated in the strongest available form".
- **Three certificates point *into* a decision principle and nothing points
  out.** `CReal.evt_attained_max_decides_sign`,
  `CReal.ivt_exact_root_decides_sign` and `CReal.lub_decides_em` each reduce a
  classical analysis conclusion **to** an order decision on ℝ (the first two
  to analytic LLPO, the third to unrestricted EM). Nobody had ever assumed
  such a principle and asked what it buys — which is exactly the measurement
  W0-2 needs.

And `creal.rs`'s own field documentation names two of the conclusions measured
below as unavailable, in prose:

- `CReal.lt` — "no `le_total` over ℝ to recover it from (`Rat.le_total` holds
  for ℚ and does not lift)";
- `CReal.abs` — "`Equiv (abs x) x ∨ Equiv (abs x) (neg x)` is a decision on
  the sign of a real and is **not** available";
- `CReal.Apart` — "`Apart x y` is *strictly stronger* than `Not (Equiv x y)`
  […] The converse is Markov's principle and is neither proved nor assumed
  here."

Three prose claims of unavailability. Each is now a theorem, on a hypothesis.

## The measurement

### 1. The reverse-mathematics map (W1-9)

`crates/axeyum-lean-kernel/src/nat_prelude/omniscience.rs`. Six theorems, no
new `Definition`, every principle spelled out **inline** in every type (never
behind an abbreviation, following `least_number.rs`'s discipline). Over a
`Bool`-valued sequence `f : Nat → Bool` — Bishop's formulation — write

```text
Hits f    :=  ∃ n, Eq Bool (f n) Bool.true
Misses f  :=  ∀ n, Eq Bool (f n) Bool.false
```

| principle | statement |
|---|---|
| **LPO** | `∀ f, Or (Hits f) (Misses f)` |
| **WLPO** | `∀ f, Or (Misses f) (Not (Misses f))` |
| **MP** (Markov) | `∀ f, Not (Misses f) → Hits f` |
| **LLPO** | `∀ f g, Not (And (Hits f) (Hits g)) → Or (Misses f) (Misses g)` |
| **EM** | `∀ (P : Prop), Or P (Not P)` |

| declaration | edge |
|---|---|
| `Nat.em_implies_lpo` | EM → LPO |
| `Nat.lpo_implies_wlpo` | LPO → WLPO |
| `Nat.lpo_implies_markov` | LPO → MP |
| `Nat.lpo_implies_llpo` | LPO → LLPO |
| `Nat.wlpo_and_markov_imply_lpo` | **WLPO ∧ MP → LPO** — the converse half |
| `Nat.lnp_unrestricted_implies_lpo` | joins the existing calibration point |

```text
  unrestricted LNP ──(least_number.rs)──> EM ──> LPO ──> WLPO
                                                  │        │
                                                  ├─> MP ──┤  (WLPO ∧ MP → LPO)
                                                  └─> LLPO
```

`wlpo_and_markov_imply_lpo` is what turns a chain into a map: **LPO factors
exactly as WLPO's decision plus Markov's witness-extraction**, so any model
separating LPO from WLPO must also separate Markov's principle.

**Proved here, and stated as proved:** the six edges above.
**Cited, not claimed:** every *non*-implication in the standard picture — LPO
is not constructively derivable (Bishop, *Constructive Analysis* ch. 1), LLPO
does not give LPO, WLPO does not give LPO, MP does not give WLPO. Each is a
**separation**, which needs a model of this kernel rather than a term in it,
and ADR-1600 records why an internal metatheorem about this kernel is
unavailable. The nearest thing the library *does* have is
`ipc_excluded_middle_not_provable`, an unprovability result for an **encoded**
propositional logic, and it is not evidence about the ambient kernel.

### 2. The deciding measurement: four classical `CReal` theorems (W0-2)

`crates/axeyum-lean-kernel/src/creal/omniscience.rs`. The hypothesis, spelled
out inline everywhere it appears:

```text
OrderDecision  :=  ∀ (x y : CReal), Or (CReal.lt x y) (CReal.le y x)
```

Written strict-on-the-left deliberately. `Or (le x y) (le y x)` is only
LLPO-strength; the strict form is LPO-strength (applied to `0` and the real
coded by a `Bool` sequence, it decides whether the sequence ever fires), and
that gap is exactly what `le_total_of_order_decision` measures below.

| declaration | conclusion | what it was before |
|---|---|---|
| `CReal.le_total_of_order_decision` | `∀ x y, Or (le x y) (le y x)` | absent; `CReal.lt`'s docs say there is no `le_total` over ℝ |
| `CReal.trichotomy_of_order_decision` | `∀ x y, Or (lt x y) (Or (Equiv x y) (lt y x))` | absent; only `Rat.lt_trichotomy` exists, because ℚ's order is decidable |
| `CReal.apart_of_not_equiv_of_order_decision` | `∀ x y, Not (Equiv x y) → Apart x y` | `CReal.Apart`'s docs name this **Markov's principle** and record it "neither proved nor assumed" |
| `CReal.abs_cases_of_order_decision` | `∀ x, Or (Equiv (abs x) x) (Equiv (abs x) (neg x))` | `CReal.abs`'s docs mark it "**not** available" |

Two of the four consume *another theorem of this file* rather than the
hypothesis directly:

```text
  OrderDecision ──> le_total ────> abs_cases
               └──> trichotomy ──> apart_of_not_equiv
```

That is the point. The question W0-2 asks is not "what does one statement
cost" but "what does **carrying** the hypothesis through a proof cost", and a
depth-1 family cannot answer it.

### 3. The number

**Every occurrence of the hypothesis, counted.**

| theorem | hypothesis binders in the type | hypothesis uses in the proof | new obligations |
|---|---|---|---|
| `Nat.em_implies_lpo` | 1 | 1 | 0 |
| `Nat.lpo_implies_wlpo` | 1 | 1 | 0 |
| `Nat.lpo_implies_markov` | 1 | 1 | 0 |
| `Nat.lpo_implies_llpo` | 1 | 2 | 0 |
| `Nat.wlpo_and_markov_imply_lpo` | **2** | 2 | 0 |
| `Nat.lnp_unrestricted_implies_lpo` | 1 | 2 | 0 |
| `CReal.le_total_of_order_decision` | 1 | 1 | 0 |
| `CReal.trichotomy_of_order_decision` | 1 | **2** | 0 |
| `CReal.apart_of_not_equiv_of_order_decision` | 1 | 1 (passed through) | 0 |
| `CReal.abs_cases_of_order_decision` | 1 | 1 (passed through) | 0 |
| **total** | **11** | **14** | **0** |

**The cost of the hypothesis route on this family is 11 binders and 14
argument positions. There are no obligations at all.**

That last column is the finding, and it is what makes this answer different
from ADR-1595's. There, the setoid route cost *three one-line obligations* —
real proof work that `Quot.sound` would have supplied. Here there is **no
analogue**. A classical hypothesis is not something you have to discharge; it
is something you carry. Carrying it costs one binder in the type and one
argument at each use, mechanically, forever, with no proof content and no
possibility of the cost growing with the depth of the development. Under the
axiom option those 25 tokens disappear and nothing else changes in the proofs.

**Readability.** The rendered type of the deepest node is:

```text
CReal.apart_of_not_equiv_of_order_decision :
  ((x y : CReal) -> Or (CReal.lt x y) (CReal.le y x))
  -> (x y : CReal) -> Not (CReal.Equiv x y) -> CReal.Apart x y
```

One extra leading binder, 42 characters. Under the axiom option it would read
`∀ x y, Not (Equiv x y) → Apart x y` and the reader would have to consult
`#print axioms` to learn that it is classical. **The hypothesis route puts
the classical assumption where the theorem is; the axiom route puts it
somewhere else.** For a library whose headline claim is about its trusted
base, that is not a wash.

### 4. Three findings that were not asked for and change the answer

**(i) The axiom option is not one axiom. It is at least three, and nobody has
sized the third.** Reviewer 03's own blocker names "excluded middle,
countable choice, and function extensionality". `funext` is absent from this
kernel and was explicitly *not* granted by ADR-1595 (reviewer 09 asked; the
answer was that its target was reachable without it and a separate decision
would be needed). `Quot.sound` is out by ADR-1595. So option (a) as reviewer
03 needs it is a three-axiom package whose third member has never been
proposed, let alone priced — and ADR-1595 already measured that the *quotient*
package alone costs five footprint names rather than one. The habit of
pricing a classical addition at "one axiom" has now been wrong twice in this
repository, measured both times.

**(ii) Option (a) retroactively devalues three existing landmark results.**
`CReal.lub_decides_em` concludes `∀ (A : Prop), Or A (Not A)` from a Bishop
supremum. Its entire content is that the classical least-upper-bound property
*costs* unrestricted excluded middle. Put EM in the environment and the
conclusion is available for free: the theorem still type-checks and still says
something formally, but it stops being a warning about a price, because the
price is already paid. The same applies to `ivt_exact_root_decides_sign` and
`evt_attained_max_decides_sign`, which land on analytic LLPO — a principle
option (a) would make free.

These are not rhetorical points. They are the three results reviewer 10 and
ADR-0603 row 2 identify as the library's most distinctive output, and option
(a) is the only choice on the table that spends them.

**(iii) Option (a) kills three gates that currently pass.** Each scans the
whole environment for a principle's *type* and fails if anything declares it,
with a same-scan positive control so a broken scan fails rather than reporting
a clean zero:

| gate | file |
|---|---|
| `excluded_middle_is_not_itself_a_declaration_anywhere_in_the_environment` | `nat_prelude/nat_prelude_tests.rs` |
| `no_omniscience_principle_is_itself_declared` | `nat_prelude/omniscience_tests.rs` (new) |
| `no_unconditional_order_decision_is_declared_over_creal` | `creal/omniscience_tests.rs` (new) |

Under option (a) all three must be deleted, not repaired — there is nothing to
repair, because the thing they assert is absent would be present. CLAUDE.md's
standing rule is that a checker that cannot fail is worse than none; the
corollary is that deleting three checkers that *can* fail is a real cost and
should appear in the ledger of the decision.

## The three options, priced in the project's own terms

### (a) Admit the classical principles as labelled axioms

| | |
|---|---|
| **buys** | classical analysis stated the way analysts write it; measure theory (W3-1), first-order completeness (W3-6) and the weak law (W2-7) proceed without threading a hypothesis; reviewer 03's subject becomes writable |
| **costs, measured** | at least three axioms (EM, countable choice, `funext`), not one, with the third never sized; the empty-footprint claim stops being a property of the library and becomes a property of a computed subset; three environment-scan gates deleted; three row-2 certificates devalued |
| **saves, measured** | 11 binders and 14 argument positions on the ten theorems built here. Zero proof obligations, because there were none |

### (b) Classical principles stay hypotheses, discharged at use

| | |
|---|---|
| **buys** | the footprint claim intact — all ten theorems here are axiom-free, read from `Kernel::axiom_footprint`; the classical assumption is visible **in the theorem's own type** rather than in a separate report; the three row-2 certificates keep their meaning; the three gates keep failing when they should |
| **costs, measured** | 11 binders, 14 argument positions, **0 obligations** |
| **costs, structural** | a classical theorem is stated as an implication, so a *user* of the library must supply the principle. For a library that is consumed by a solver rather than by a human writing Lean, this is where the cost actually lands, and it is not measured here |
| **risk** | a theorem may exist that genuinely cannot be stated this way. Nothing in this experiment rules one out — see the reversal trigger below |

### (c) Admit them in a labelled second tier

| | |
|---|---|
| **buys** | both claims, if the tiering is honest and enforced |
| **costs** | the same real mechanism ADR-1595 priced and declined: `axiom_footprint` already returns the names, so the tier boundary has to live in the fact ledger *and* in a gate that refuses tier-2 evidence for a tier-1 fact. That gate does not exist |
| **the trap** | identical to ADR-1595's: once the axiom is in the environment, nothing but discipline keeps a nominally-constructive proof from routing through it, and the tier would have to be mutation-tested — delete one guard, require exactly one test to die — before it could be quoted |
| **when it becomes right** | when a measured theorem is shown unreachable by route (b). Not before |

## Decision

**Option (b). Classical principles enter this library as explicit hypotheses
in the statements that need them. No excluded middle, no choice, no `funext`
and no order decision is admitted as a kernel axiom.**

Three judgements, stated so they can be argued with:

1. **A hypothesis costs a constant; an axiom costs a claim.** The measurement
   says the hypothesis route's overhead is 11 binders and 14 arguments and
   does not grow with depth — the two depth-2 `CReal` theorems cost exactly
   what the depth-1 ones cost. The axiom route's overhead is that the
   headline metric changes shape: "axiom-free" becomes "axiom-free except in
   the analysis shelf", which a referee has to be told rather than shown.
2. **The classical statement is *more* informative as an implication.**
   `CReal.abs_cases_of_order_decision` says precisely what the classical `abs`
   dichotomy costs. As an axiom-backed theorem it would say only that it
   holds. For a library whose distinctive output is calibration — reviewer
   10's "you have one calibration point and the technique to make it a map" —
   the implication *is* the result.
3. **Option (a) is the only choice that spends an uncontested axis.** ADR-1595
   used this argument for quotients and it applies here with more force: an
   empty trusted base across a real-analysis shelf is a thing this library can
   say that Mathlib cannot, and the measured price of keeping it is 25 tokens.

**Reversible on evidence, not on preference.** The trigger is a *named,
attempted* theorem shown to be unreachable as an implication, with the
obstruction stated as a specific obligation the kernel could not discharge.
This ADR's own method is the template. Two candidate shapes are known in
advance and should be watched for:

- a theorem whose classical hypothesis cannot be **stated** without a former
  the kernel lacks (`funext` is the live candidate; countable choice over ℝ is
  statable today, since `Exists` over a function type is already used by
  `Nat.cantor_diagonal`);
- a development where the hypothesis has to be threaded through so many layers
  that the binder count stops being a constant. **The number to watch is the
  ratio of hypothesis uses to theorems: 14 / 10 = 1.4 here.** If a shelf
  reports that above roughly 3, re-open this.

## What changes downstream

| roadmap item | under **(b)** — recommended | under (a) |
|---|---|---|
| **W1-9** extend the reverse-mathematics map | **landed** — six edges, empty footprint | would be pointless: with EM an axiom, every edge is discharged and the map measures nothing |
| **W3-1** measure and the Lebesgue integral on ℝ | **unblocked, with a stated shape.** σ-algebras, measurability and the convergence theorems are stated over `CReal` with the classical principle each one actually needs as a binder. This is *more* work to design and less to prove; the measurement here says the per-theorem cost is one binder | proceeds as classically written; every measure-theoretic fact carries the axioms |
| **W3-6** first-order model theory, toward completeness | **unblocked for soundness; completeness carries its choice principle as a hypothesis.** Reviewer 10.3 already calls completeness "a good test of the classical-axiom policy" — under (b) the test is that Henkin's construction states its choice principle explicitly, which is the standard reverse-mathematics treatment | completeness proved outright from an admitted choice axiom |
| **W2-7** the weak law of large numbers | **unblocked.** WLLN over a finite probability space needs no classical principle at all; it is gated on W1-10 (generalizing finite probability over `AlgS.OrderedRing`), not on this ADR. **This ADR removes W0-2 as a blocker for W2-7 and does not add one** | same |
| **W2-1/W2-3** metric spaces, Bishop compactness | unaffected — Bishop's development is constructive by design | unaffected |

Reviewers:

- **03 classical analysis** — its stated trigger is "W0-2, W0-3, W3-1 land".
  W0-2 is now written, and it is written *against* this reviewer's implied
  preference. The reviewer is owed the honest note that option (a) was priced
  and declined on measurement, and the honest concession that **(b) does not
  give it what it asked for**: it cannot write classical analysis the way an
  analyst writes it. What it gets is that the shelf is unblocked, with a
  stated shape and a measured per-theorem cost. Its verdict should be
  expected to stay *unmoved* until W3-1 actually lands.
- **08 probability** — unblocked and never really blocked: W2-7 needs W1-10,
  not this. The measure-theoretic half (08.5) follows W3-1 under (b) as under
  (a).
- **10 logic and foundations** — its first item (W1-9) is landed here, with
  the separations honestly marked as citations rather than claims. Its third
  item (completeness) has a stated shape under (b). This is the reviewer
  option (b) serves best, and it is the reviewer already most interested in
  the trusted base.
- **12 the chair** — its trigger is that W0-1 and W0-2 are *written*. W0-1 is
  ADR-1595. This is W0-2. Both are now written.

## What the empty-footprint headline costs under option (a)

The metric that would move is the one CLAUDE.md calls the product: *"the
trusted base, not the output volume […] assumptions remaining per prelude"*,
reported by `scripts/validate-facts.py` and `nat_axiom_inventory
--require-axiom-free`.

Measured today, after this lane landed (`python3 scripts/validate-facts.py`,
2026-09-04): **2,768 facts, 0 errors; 2,497 proved; 2,397 on the
`kernel-lean` route, of which 2,395 are axiom-free.** All ten theorems built
for this ADR are in that 2,395.

Under (a) that number does not fall to zero and it does not stay where it is.
It **changes kind**. Today the claim is a single number read from
`Kernel::axiom_footprint` over the whole ledger, and a competitor can neither
inflate it nor dispute it. Under (a) the claim becomes "axiom-free except for
the following labelled set, in the following shelves", which is:

- **not checkable by one command**, because the exemption is a policy about
  which axioms are acceptable rather than a property of the environment;
- **not comparable over time**, because the exempt set grows;
- **not a Pareto axis**, because Mathlib is also axiom-free-except-for-a-
  labelled-set, and its labelled set is the same three axioms. The uncontested
  axis exists *only* while the set is empty.

That is the whole price, and it is why the 25 tokens the hypothesis route
costs are worth paying.

## Verification

Everything in this ADR is reproducible from the tree:

```sh
# the six-edge map over Nat, with its negative controls (8 tests, nonzero)
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib nat_prelude::omniscience -- --test-threads=4

# the four CReal measurement theorems (6 tests, nonzero, 51.80 s)
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --lib creal::omniscience -- --test-threads=4

# all ten types and all ten footprints, read from the kernel rather than prose
cargo run -q --release -p axeyum-lean-kernel \
  --example kernel_declaration_projection \
  -- --require-declaration CReal.abs_cases_of_order_decision \
     --require-kind theorem

# the ten declarations, read from the kernel
cargo run -q --release -p axeyum-lean-kernel --example shape_search \
  -- --name-contains lpo --min 5
cargo run -q --release -p axeyum-lean-kernel --example shape_search \
  -- --include-constructed --name-contains order_decision --expect 4

# the absence claims this ADR leans on (each prints its own positive control)
cargo run -q --release -p axeyum-lean-kernel --example shape_search \
  -- --include-constructed --ns CReal --name-contains le_total --expect-absent
cargo run -q --release -p axeyum-lean-kernel --example shape_search \
  -- --name-like omniscience --expect-absent   # before this lane landed

# the headline metric
python3 scripts/validate-facts.py
```

## Related

- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) —
  the sibling decision, taken the same way on the same day, and the source of
  the "it is one axiom" pricing error this ADR finds for a second time.
- [ADR-1600](adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md)
  — what is trusted and what is not, and why a separation result cannot be
  internal.
- [ADR-0603](adr-0603-classical-theorems-land-as-graded-statement-families.md)
  — graded statement families; the row-2 certificates this ADR measures are
  its output, and option (b) is what keeps row 2 meaningful.
- [ADR-0512](adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
  — ℝ as a Bishop setoid, which is why `CReal`'s order is not decidable in the
  first place.
- [The department roadmap](../../math-department/00-roadmap.md) — W0-2, W1-9,
  and the C4 convergence this closes.
- [03 classical analysis](../../math-department/03-classical-analysis.md)
  § The blocker — the question this ADR answers, stated by the reviewer whose
  subject it is.
- [10 logic and foundations](../../math-department/10-logic-and-foundations.md)
  — the reverse-mathematics request, and the trusted-base reading of the
  library.
