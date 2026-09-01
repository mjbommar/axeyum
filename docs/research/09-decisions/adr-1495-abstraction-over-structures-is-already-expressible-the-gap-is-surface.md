# ADR-1495: Abstraction over algebraic structures is already expressible — the gap is surface, and it hid a `Type : Type` hole

Status: accepted
Date: 2026-09-01
Index-summary: `docs/curriculum/foundational-books/axler.md` closes roughly half
of Axler's chapters as `X-TA` — "no polymorphism in this kernel's term language,
so 'for every vector space' cannot even be **stated** … permanent absent a change
to the kernel's term language". **That is false**, measured three ways: the
unbundled telescope form was already admitted (ADR-0865, 2026-08-30), a
17-field bundled `Field` with a `Sort 1` carrier as a FIELD admits at `Sort 2`
with selectors by large elimination and a DERIVED cancellation theorem
quantified over it, and a `VecSp` bundle **carrying the `Field` bundle**, with
`smul` typed through two nested projections, admits a derived theorem too —
every one axiom-free, first attempt, with content controls refused. So Axler
Ch.1–2 is stateable. The gap is **surface**: 1,774 lines of hand-built kernel
terms bought one `Field`, one `VecSp`, 13 selectors and 2 theorems. The
decision is therefore **YES to the statement class, NO to a hierarchy or
typeclass resolution, and the mechanism is gated on one named first consumer**
— `Nat.Fin` still has **zero non-test consumers** (re-verified today with a
positive control), and a mechanism nobody adopts is the outcome to avoid.
Measured demand for the second rung: **49 lemma names proved over 3+ carriers,
23 over 4+, 15 over all five** of `Nat`/`Int`/`Rat`/`CReal`/`Complex`. One hard
constraint found on the way: `CReal` states its laws with setoid `Equiv`, not
`Eq`, so a bundle must carry its own equality relation or a quotient will cost
`Quot.sound` and move `creal` off zero axioms. Separately and more seriously,
the probe's own universe control **did not fire**: `add_inductive` never
enforced Lean's constructor-field universe constraint, so `U : Sort 1` with
`mk : Sort 1 → U` plus large elimination made `Sort u` a retract of an
inhabitant of `Sort u`. Fixed here; two pinned fixtures had been asserting that
Lean-illegal inductives ADMIT, which is why it survived.
Index-status: accepted

## Context

`docs/research/11-design-review/2026-09-01-the-abstraction-question-has-never-been-asked.md`
measures that the repository has argued the *aggregate* question 281 times and
the *abstraction* question zero times, and identifies why: **the fact ledger is
a statement-level mechanism.** A proposition that cannot be written never enters
the inventory, never gets screened, and therefore never appears as missing. The
queue can be green while a branch of mathematics is out of reach.

The artifact that surfaced it is a curriculum.
[`docs/curriculum/foundational-books/axler.md`](../../curriculum/foundational-books/axler.md)
audits all ten chapters of *Linear Algebra Done Right* and tags roughly half
`X-TA`, defined in its own legend as:

> unavailable for a **type-theoretic abstraction** reason: the statement
> quantifies over an arbitrary vector space, field, or linear map as a
> first-class object, and this kernel has no structure/typeclass mechanism to
> express that quantification at all — not "not yet proved", but no *statement*
> exists to prove. **This is permanent absent a change to the kernel's term
> language**, not a proof debt.

and at Chapter 1:

> There is no polymorphism in this kernel's term language, so "for every vector
> space" cannot even be **stated**, let alone proved or refuted. **This is the
> chapter that sets the pattern for the rest of the table.**

[ADR-1310](adr-1310-the-aggregate-absence-is-an-inventory-and-a-fold-is-not-a-type.md)
decided "add no aggregate" and was right on its evidence, but its scope was
**containers** (`List` / `Fin`-indexed families / `Prod`) driven by one theorem,
and it named its own revisit condition. This is a different axis: not *which
container* but *is there any mechanism by which a statement quantifies over a
structure*. Nothing in ADR-1310 addresses it.

## Measurement 0: the question was half-answered nine months of lane-days ago, and the grep missed it

The deficiency note reports "ADRs on polymorphism / typeclasses / structures: 0
(grep returns only false positives)". That count is right about ADR *titles* and
wrong about the tree.

[`crates/axeyum-lean-kernel/examples/g4_pilot_generic_assoc_probe.rs`](../../../crates/axeyum-lean-kernel/examples/g4_pilot_generic_assoc_probe.rs)
(2026-08-30, recorded in [ADR-0865](adr-0865-two-of-three-g4-pilots-retain-the-graph-ranking-one-category-untested.md)
and `docs/plan/status/l2-g4-pilot-clusters.md`) already built and admitted

```
∀ (α : Sort 1) (op : α → α → α),
  (∀ a b c, op (op a b) c = op a (op b c)) → ∀ a b c, op (op a b) c = op a (op b c)
```

through `Kernel::add_declaration`, with a negative control (the same
identity-shaped term against a commutativity conclusion) correctly refused. That
lane's own finding was the right one and was never propagated:

> A raw, non-bundled, `Sort`-quantified statement over an arbitrary carrier and
> an arbitrary binary operation is ALREADY representable and accepted — it
> always was. What is missing is the bundled **ergonomics**, not raw
> statability.

So the **unbundled telescope** half was settled. What was never tested is the
**bundled** half — and that is the half `axler.md`'s `X-TA` verdict actually
rests on, because "for every vector space `V` over every field `F`" is not a
telescope of loose operations, it is a structure passed as one object.

## Measurement 1: the kernel already admits dependent records with proof fields

Read before writing any probe:

| declaration | shape |
| --- | --- |
| `Rat` (`int_prelude/rat.rs:106`) | one-constructor inductive in `Type 1` whose constructor carries **two data fields and two proof fields** (`1 ≤ den`, `gcd (natAbs num) den = 1`) |
| `Complex` (`complex.rs:3996`) | one-constructor inductive in `Type 0`, projections by large elimination |
| `Exists.{u}`, `Acc.{u}` (`prelude.rs:1307`, `:1384`) | universe-polymorphic, `Sort u` **parameter** |
| `WellFounded.fix.{u,v}` (`prelude.rs:215`) | universe-polymorphic fixpoint with a checked unfolding equation |

A structure with laws is therefore not a new idea here; `Rat` is one. What had
never been tried is a carrier as a **field** rather than a parameter, which is
the thing that makes a bundle quantifiable.

## Measurement 2: a full `Field` bundle, and a DERIVED theorem quantified over it

[`examples/bundled_structure_probe.rs`](../../../crates/axeyum-lean-kernel/examples/bundled_structure_probe.rs).
`AbsProbe.Field` is a one-constructor inductive in `Sort 2` whose constructor
carries a `Sort 1` **carrier as a field**, seven operations
(`zero one add mul neg inv`) and **ten laws**, including one with a hypothesis
(`(a = 0 → False) → a * a⁻¹ = 1`) and one that is itself a refutation
(`1 = 0 → False`). Seventeen fields.

```
stage 1: AbsProbe.Field, one constructor, 17 fields
  universe control: PASS -- Sort 1 refused: ConstructorFieldUniverseTooBig { … }
  add_inductive(AbsProbe.Field : Sort 2): PASS
  recursor generated (88 chars)
stage 2: selectors
  carrier : Field -> Sort 1 (large elimination): PASS
  zero / add / neg: PASS
  addAssoc / zeroAdd / negAdd (laws through selectors): PASS
  iota control: PASS -- carrier (mk A ...) def_eq A
stage 3: theorem quantified over the structure
  RESULT: PASS -- AbsProbe.Field.addLeftCancel admitted
  content control: PASS -- wrong conclusion refused
axiom_footprint(AbsProbe.Field.addLeftCancel) = []
ALL STAGES AND CONTROLS AS EXPECTED
```

The admitted theorem, rendered by the kernel:

```
(x0 : AbsProbe.Field) -> (x1 x2 x3 : AbsProbe.Field.carrier x0) ->
  Eq.{1} (AbsProbe.Field.carrier x0)
         (AbsProbe.Field.add x0 x1 x2) (AbsProbe.Field.add x0 x1 x3)
  -> Eq.{1} (AbsProbe.Field.carrier x0) x2 x3
```

This is **derived, not projected**: additive left cancellation is a seven-step
transport chain through `addAssoc`, `negAdd` and `zeroAdd`, none of which states
it. Three controls make the PASS non-vacuous, and all three fire:

- **Content control.** The same proof term against the conclusion `a = c`,
  which does not follow from `a + b = a + c` in any field with more than one
  element, is REFUSED.
- **Iota control.** `carrier (Field.mk A …)` must `def_eq` `A`, or a selector
  could be admitted and mean nothing.
- **Universe control.** The same bundle at result universe `Sort 1` must be
  refused. **This one did not fire on the first run** — see Measurement 5.

Every stage passed on the first attempt. Nothing about it was delicate.

## Measurement 3: a bundle carrying another bundle — Axler Ch.1–2 is stateable

A `Field` alone does not settle the driver. "A vector space `V` over a field
`F`" needs strictly more: a bundle whose field is *another bundle*, with later
fields whose types are stated **through a projection of that field**.

[`examples/module_over_field_probe.rs`](../../../crates/axeyum-lean-kernel/examples/module_over_field_probe.rs)
builds exactly that:

```
AbsMod.VecSp : Sort 2
  mk : (F : AbsMod.Field)                            -- a BUNDLE as a field
       (V : Sort 1)
       (addV : V → V → V)
       (smul : AbsMod.Field.carrier F → V → V)       -- through a PROJECTION
       (oneSmul : ∀ v, smul (AbsMod.Field.one F) v = v)
       (smulAdd : ∀ a v w, smul a (addV v w) = addV (smul a v) (smul a w))
    → AbsMod.VecSp
```

and admits, first attempt:

```
(x0 : AbsMod.VecSp) -> (x1 x2 : AbsMod.VecSp.carrier x0) ->
  Eq.{1} (AbsMod.VecSp.carrier x0)
    (AbsMod.VecSp.addV x0
       (AbsMod.VecSp.smul x0 (AbsMod.Field.one (AbsMod.VecSp.scalars x0)) x1)
       (AbsMod.VecSp.smul x0 (AbsMod.Field.one (AbsMod.VecSp.scalars x0)) x2))
    (AbsMod.VecSp.addV x0 x1 x2)
```

derived by chaining `smulAdd` backwards with `oneSmul` — two laws, not one.
`VecSp.smul`'s own type resolves through **two nested projections**
(`AbsProbe.Field.carrier (AbsMod.VecSp.scalars s)`) and the kernel discharges it
by iota with no help. `axiom_footprint` empty. Content control: the same proof
term against `= addV w v`, which needs a commutativity this structure never
assumes, is REFUSED.

**So `axler.md`'s Chapter 1 verdict is false and its `X-TA` legend is wrong**,
in the direction that permanently closes chapters. The chapters are not
type-theoretically unreachable; they are unbuilt.

## Measurement 4: the universe question, answered

A bundle carrying a `Sort 1` carrier lives at `Sort 2`, and this kernel supports
that: the recursor's motive level is a fresh universe parameter
(`inductive.rs:2751`), large elimination is available whenever the result
universe is provably nonzero (`inductive.rs:1753`), and `Field.carrier :
Field → Sort 1` is admitted by instantiating the recursor at motive level 2.
Nothing about universes obstructs the mechanism.

## Measurement 5: the universe control did not fire, and that is a soundness finding

The probe's universe control asserted that the same seventeen-field bundle,
declared at result universe `Sort 1`, must be refused. It was accepted.

[`examples/inductive_universe_probe.rs`](../../../crates/axeyum-lean-kernel/examples/inductive_universe_probe.rs)
isolates it to the smallest shape. Before the fix:

```
positivity control: PASS -- refused: NonPositiveInductiveOccurrence { … }
stage 1: AbsProbe2.U : Sort 1 with `mk : Sort 1 -> U` ACCEPTED
stage 2: `el : U -> Sort 1` by LARGE elimination ACCEPTED
stage 2: RETRACTION HOLDS -- el (mk X) def_eq X
stage 3: AbsProbe2.V : Sort 2 with `mk : Sort 2 -> V` ACCEPTED too
```

`mk` injects `Sort u` into an inhabitant of `Sort u` and `el` projects it back,
definitionally. That is `Type : Type` — the precondition for Girard's paradox.
The positivity control passes in the same run, so the checker was running; this
one constraint was simply absent. **This probe does not derive `False`**;
Hurkens' paradox is a separate and much larger undertaking, and no such claim is
made here.

The cause is exact. `inductive.rs` already infers each constructor field's
`domain_level` and uses it **only** to compute `field_is_proof`; it is never
compared against the family's `result_level`. Lean's `check_constructor` makes
that comparison. The fix is five lines beside the existing computation,
exempting `Prop` because it is impredicative, plus
`KernelError::ConstructorFieldUniverseTooBig`.

**Nothing in the tree declared such an inductive**, so no landed result was
affected and no `axiom_footprint` moves;
`prelude_theorem_inventory --release --include-constructed` exits 0 with 11,969
rows after the fix, meaning every prelude still builds. This was a checker
weakness, not a wrong result.

### Why it survived: two pinned fixtures asserted that Lean-illegal inductives admit

Both are the kernel's most systematic inductive-admission suites, and this is
the lesson worth carrying:

- `tests/mutual_inductive_group_grammar.rs` — 720 generated cases with a pinned
  `descriptor-fnv1a64`. Every generated constructor field's domain is `Sort 1`,
  while its `type`-sorted families lived at `Sort 1`. All **360** `type` cases
  were Lean-illegal and every one was asserted to ADMIT. Repaired by putting
  the `type` families at `Sort 2`; the pinned summary and digest are unchanged,
  because the descriptor records counts and labels, not field domains.
- `tests/kernel_seam_fuzz.rs` — its data field has type `Prop`, which lives at
  `Sort 1`, under families at a bare universe **parameter** (`Sort u`,
  `max u 0`, `imax 1 u`). Nothing is provably at or below a bare `u`, so such a
  family can carry no non-proof field at all — a fact about Lean, not about the
  fuzz. Data fields are clamped to zero for exactly those shapes; every shape
  and proof-field count stays in the population.

A fixture that encodes the wrong expectation is a checker that cannot fail,
arriving through the door marked "systematic coverage". The new test
`reject_ctor_field_universe_above_result_universe` carries the refusal **plus
two positive controls** — the Lean-legal form one universe up must be ACCEPTED,
and a `Prop`-valued family storing a `Sort 1` field must also be accepted (that
is exactly `Exists`/`Acc`, which this prelude declares) — so it is a measurement
rather than a blanket refusal.

## Measurement 6: the counter-evidence, re-verified rather than inherited

ADR-1310's strongest argument is that `Nat.Fin` landed and nothing adopted it.
Re-measured today, with a positive control in the same command:

```
Nat.Fin / nat_fin / NatFin, files under src/ …………………… 10
  of which: the declaring module (nat_prelude/finite.rs)   1
            doc comments only                              5
            test files                                     1  (all 6 hits)
  code consumers outside finite.rs and tests ……………………… 0
control: p.succ referenced outside its own module ……………  yes (tc.rs, tests)
```

**Zero non-test consumers, still.** The finite-combinatorics apparatus — the
development with the best possible reason to use an indexed type — declined it
and stayed with bounded `Nat` quantifiers. That prior is intact and is the
outcome this ADR is designed to avoid repeating.

## Measurement 7: the demand for the second rung, and it is real

Distinct lemma **names** in the constructed environment (11,969 rows,
`--include-constructed`), grouped by suffix across the five algebraic carriers:

```
distinct suffixes ……………………… 1838
proved over ≥3 carriers ………………  49
proved over ≥4 carriers ………………  23
proved over all 5 ……………………………  15
```

The fifteen that exist over `Nat`, `Int`, `Rat`, `CReal` and `Complex` alike are
`add_assoc`, `add_comm`, `add_zero`, `mul_assoc`, `mul_comm`, `mul_one`,
`mul_zero`, `left_distrib`, `pow_zero`, `pow_succ`, `pow_add`, `sumRange_zero`,
`sumRange_succ`, `sumRange_add`, `sumRange_congr`. `add_neg` correctly appears
at **four** carriers and not five — `Nat` is not a ring — which is a useful
self-check that the grouping is measuring something.

Caveat stated plainly, because the number is otherwise misleading: **a shared
name is not a shared statement.** See the next section.

## The constraint that will decide how a bundle is designed: `CReal` is a setoid

`Rat`, `Int`, `Nat` and `Complex` state their laws with `Eq`.
**`CReal.add_comm` is `∀ x y, Equiv (add x y) (add y x)`** (`creal.rs:219`) — a
Bishop setoid equivalence, not propositional equality, and that is deliberate
(ADR-0512; `creal` measures 0 axioms precisely because it is *not* a quotient).

So a bundled algebraic structure here cannot state its laws with `Eq` and still
admit `CReal` as an instance. Two ways out, and they have different prices:

- **Carry the equality.** The bundle gets a field `eq : A → A → Prop` plus
  reflexivity/symmetry/transitivity and congruence for each operation. Free in
  axioms; more fields, and every law is stated through the carried relation.
- **Quotient the setoid.** `Quot.sound` is in the trusted surface
  (`lean_pp.rs` filters `axiom_footprint` to `Axiom | Opaque | Quotient`), so
  this moves `creal` off zero and would surrender the headline metric for the
  reals.

The first is the only acceptable route, and it should be decided before anyone
writes a `Field` structure — not discovered halfway through.

## What the surface actually costs

The three probes total **1,774 lines** of Rust and buy: one `Field`, one
`VecSp`, thirteen selectors and two theorems. There is no `structure` command,
no projection sugar, no instance resolution, no elaboration — every `Pi`,
`Lam`, recursor application and universe level is written by hand. The
dev-helper layer does not help, because it hardcodes a carrier: `NatOps::congr`
concludes at `Nat`, `IntDev::irefl` is Int-typed, and CLAUDE.md records three
separate lanes bitten by that in one day.

**That ratio is the whole argument.** The kernel is not the bottleneck and never
was; a builder layer is, and a builder layer is ordinary engineering with an
ordinary adoption risk.

## Decision

**Yes to the statement class. No to a hierarchy. The mechanism is gated on one
named first consumer.**

1. **Record that the kernel expresses abstraction over structures** — unbundled
   telescopes (ADR-0865), single-carrier bundles, and bundles over bundles — at
   **zero** axiom cost, and correct every document that says otherwise. In
   particular `axler.md`'s `X-TA` legend must stop saying "permanent absent a
   change to the kernel's term language"; the correct reading is **unbuilt
   surface**, and roughly half of Axler's chapters change category.

2. **Build no typeclass system, no instance resolution, and no hierarchy of
   structures.** There is no consumer for any of it, and `Nat.Fin` is what
   happens when a mechanism lands ahead of one.

3. **First consumer, and the gate: the carrier-generic congruence/transport
   layer.** It needs only the *unbundled* half, it is already proved to work,
   and it already has a measured duplication count. G4 pilot 2
   (`examples/g4_pilot_generic_congr_probe.rs`) showed a carrier-generic
   `congr_arg` reproduces `NatOps::congr`'s **byte-identical `ExprId`** — drop-in
   reuse, not a parallel implementation. The running metric is the count of
   files carrying carrier-specific `congr`-shaped helpers
   (`congr_nat_to|congr_bool_to_nat`), measured at **4** on 2026-08-30. It must
   fall, and no new per-carrier congruence helper should be added while a
   generic one exists.

4. **Second rung, conditional on (3) landing AND being consumed by a lane that
   did not build it:** a bundled algebraic structure carrying its own equality
   relation, with `Rat`, `CReal` and `Complex` as instances, aimed at the 15
   lemma names proved over all five carriers. Design the carried equality
   first (see the setoid constraint above). Gate: at least one of those fifteen
   is proved once and consumed at two carriers.

5. **Not now:** vector spaces, modules, spans, bases, dimension, categories.
   Measurement 3 shows they are *stateable*; nothing shows anyone wants them,
   and Axler Ch.2 also needs the aggregate ADR-1310 declined. Revisit when
   rung 4 has an adopter.

6. **Abandonment condition, stated in advance.** If (3) lands and nothing
   outside its own tests consumes it, stop and record it as a second `Nat.Fin`
   rather than continuing to rung 4. The metric in (3) is exactly the thing
   that would show this.

7. **The kernel guard lands now, independently of any of the above**, because
   it is a soundness fix and not an abstraction feature.

## Consequences

- `docs/curriculum/foundational-books/axler.md` needs its legend and its
  Chapter 1/2/7/9 rows re-graded from `X-TA` ("permanent") to an
  unbuilt-surface category. That is a documentation task, not a proof task, and
  it is the single highest-value follow-up here: the current text tells every
  future lane that half of linear algebra is out of reach.
- The deficiency note's framing — that a statement-level ledger is structurally
  blind to what it cannot express — is confirmed and is *worse* than it says:
  the tree already had the capability, a pilot had already demonstrated half of
  it, and the curriculum still recorded it as impossible. The blind spot is not
  only that the ledger cannot see unstateable propositions; it is that nothing
  connects a probe's finding back to the documents that assert the opposite.
- `Kernel::add_inductive` is now closer to Lean's `check_constructor`. Any
  future inductive whose field type sits above its result universe is refused,
  with `Prop` exempt.
- Two fixtures were repaired. Anyone adding generated inductive cases must now
  respect the universe constraint; both fixtures document why in place.

## What this does NOT change

- **The aggregate question is untouched.** ADR-1310 stands: no `List`, no
  `Finset`, no `Prod`. A bundle does not give you a multiset, and Axler Ch.2's
  bases and dimension need one.
- **The constructive boundary is untouched.** No excluded middle, no choice, no
  `funext`. A structure-quantified statement is subject to exactly the same
  boundary its concrete instances are.
- **No claim is made that `False` is derivable** from the pre-fix kernel. The
  retraction is the standard precondition; deriving the paradox was not
  attempted.
- **`Nat.Fin` is not rehabilitated.** It still has zero non-test consumers and
  this ADR adds no reason to use it.

## Evidence

| what | where |
| --- | --- |
| bundled `Field` + derived theorem + 3 controls | `crates/axeyum-lean-kernel/examples/bundled_structure_probe.rs` |
| bundle over bundle (`VecSp` over `Field`) | `crates/axeyum-lean-kernel/examples/module_over_field_probe.rs` |
| the `Type : Type` retraction, before and after | `crates/axeyum-lean-kernel/examples/inductive_universe_probe.rs` |
| unbundled telescope (prior art) | `crates/axeyum-lean-kernel/examples/g4_pilot_generic_assoc_probe.rs`, ADR-0865 |
| byte-identical generic `congr_arg` (prior art) | `crates/axeyum-lean-kernel/examples/g4_pilot_generic_congr_probe.rs`, ADR-0865 |
| the guard | `crates/axeyum-lean-kernel/src/inductive.rs`, `KernelError::ConstructorFieldUniverseTooBig` in `src/tc.rs` |
| the guard's test, with two positive controls | `reject_ctor_field_universe_above_result_universe`, `src/inductive/inductive_tests.rs` |

Verification run for the guard: `--lib inductive` 49 passed; twelve
inductive-related integration suites 72 passed;
`prelude_theorem_inventory --release --include-constructed` exit 0 with 11,969
rows; `clippy --release -p axeyum-lean-kernel --all-targets -D warnings` clean;
all three probes exit 0 with every control firing. **Not run:** the full
workspace `--lib` and `--tests` sweeps, both killed at a 10-minute wall
(exit 143, SIGTERM) partway through the `creal`/`complex` suites; neither
reached a `test result:` line.
