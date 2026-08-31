# ADR-1240: Index 0 is filled — and an inductive `Prop` gives up the evaluation test, so something has to replace it

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1220 measured that cycle index 0 was the binding slot for
draw 16 and named `Mathlib.Computability.Primrec.Basic` (11 rows, zero boundary
rows, no churn, no stale review) as the one candidate that fits it, needing
`Nat.Primrec` and `Nat.casesOn`. Both are now declared, construction only
(ADR-0653): `Nat.casesOn.{u}` as a universe-polymorphic definition over
`Nat.rec`, and `Nat.Primrec` as a seven-constructor inductive `Prop` whose
`left`/`right` constructors use ADR-1220's `Nat.unpairLeft`/`unpairRight`
because Mathlib's `Prod`-returning `Nat.unpair` is not available here. Every
ADR-1220 figure reproduced against a freshly rebuilt `shape_search` and the real
`select()`/`assign_partitions()`/`screen_family()`/`is_closed_evaluation`: pool
11, boundary rows **0 of 10** read verbatim, frozen-family churn **0 of 42**,
stale reviews **0 of 4**. Post-declaration the environment is **2706**, exactly
+10, and layout RP puts `natural-primitive-recursion` at index 0 held-out with
R9/R10/R12 passing and R11 clean on every hard signal; the only remaining
refusal is R11's authorable disclosure, which is the draw lane's review step and
is deliberately not performed here. **The substantive finding is not the
declaration.** `Nat.Primrec` is an inductive `Prop`, so it admits no evaluation
test — the safeguard every definition in this repository leans on, because the
kernel cannot tell a `Definition` is wrong. What replaces it: the predicate does
not evaluate but its constructor INDICES do, so the evaluation test is recovered
one level in; plus closed derivations assembled from the real constructors, and
a binder-count assertion. Five mutants, four killing exactly one test each.
Held-out `166`, `settled=0`, before and after; no fact moved partition and none
was registered.

Related: ADR-1220 (the index-0 measurement this executes, and the two screens it
introduced), ADR-1160 (the boundary-equation READING, and the index-3 unblock),
ADR-1115 (the pre-declaration closed-evaluation check), ADR-1100 (the positional
framing ADR-1220 inverted), ADR-1060 (`Nat.avg`/`Nat.pair`), ADR-0653
(construction-only unblocks), ADR-0695/ADR-0950 (R12), ADR-0768 (R11 and its
disclosure review), ADR-0542 (the amendment ledger)

## What was verified before anything was written

`shape_search --release` was rebuilt in this worktree rather than trusted from a
prebuilt binary — the documented stale-index hazard, where a false ABSENT is the
expensive verdict. Session start: **2696** declarations against the committed
snapshot's 2693, so three had landed from the `first-supplementary-law` lane
after ADR-1220's measurement.

Against that tree, with the real machinery
(`docs/research/09-decisions/adr-1240-index-zero-screen.py`, which loads
`gen-autogenesis-nursery-refill.py`, `check-holdout-adjacency.py` and
`check-holdout-closed-evaluation.py` by path and calls the actual functions —
`propose-nursery-refill.py` is not used as a candidate space, per ADR-1160):

| ADR-1220 claim | reproduced |
| --- | --- |
| pool 11 with `Nat.Primrec` + `Nat.casesOn` | **yes**, 11 |
| pool 0 without them | **yes**, 0 |
| `Nat.unpaired` already admissible | **yes** (ADR-1220 landed it) |
| boundary rows in the drawn ten: 0 | **yes**, read verbatim — see below |
| frozen-family drawn-ten churn: none | **yes**, 0 of 42 families |
| stale recorded review: none | **yes**, 0 of 4 reviews, 0 of 16 held-out families refused |
| `G7 queue-below-floor`: 4 against a floor of 10 | **yes**, unchanged |

Two things the brief said that were **wrong**, both harmless and both worth
recording:

- **`check-autogenesis-nursery.py` is GREEN, not red.** ADR-1220 verified it red
  on `main` at `69eb494e9` and reported it as a standing failure unrelated to
  that lane. It exits 0 here, before and after, on the merged tree. Someone
  fixed the cross-population partition leak in between. The brief inherited
  ADR-1220's reading, which was accurate when written.
- **The brief's `held_out=166 settled=0 PASS` is right**, and so is every other
  baseline it names.

## The drawn ten, read verbatim

ADR-1160's rule is that the pool check has to be a READING as well as a run of
the classifier, because `is_closed_evaluation` is binder-free by construction:
a `∀`-quantified defining equation is settled by reduction and still reports
clean. All ten of these are `is_closed_evaluation = False`, and reading them
confirms that is the right answer rather than a blind spot:

```text
[0] Nat.Primrec.add       Nat.Primrec (Nat.unpaired fun x1 x2 => x1 + x2)
[1] Nat.Primrec.casesOn'  ∀ {f g : ℕ → ℕ}, Nat.Primrec f → Nat.Primrec g →
                            Nat.Primrec (Nat.unpaired fun z n =>
                              Nat.casesOn n (f z) fun y => g (Nat.pair z y))
[2] Nat.Primrec.casesOn1  ∀ {f : ℕ → ℕ} (m : ℕ), Nat.Primrec f →
                            Nat.Primrec fun x => Nat.casesOn x m f
[3] Nat.Primrec.const     ∀ (n : ℕ), Nat.Primrec fun x => n
[4] Nat.Primrec.mul       Nat.Primrec (Nat.unpaired fun x1 x2 => x1 * x2)
[5] Nat.Primrec.of_eq     ∀ {f g : ℕ → ℕ}, Nat.Primrec f →
                            (∀ (n : ℕ), f n = g n) → Nat.Primrec g
[6] Nat.Primrec.pow       Nat.Primrec (Nat.unpaired fun x1 x2 => x1 ^ x2)
[7] Nat.Primrec.prec1     ∀ {f : ℕ → ℕ} (m : ℕ), Nat.Primrec f →
                            Nat.Primrec fun n =>
                              Nat.rec m (fun y IH => f (Nat.pair y IH)) n
[8] Nat.Primrec.pred      Nat.Primrec Nat.pred
[9] Nat.Primrec.swap      Nat.Primrec (Nat.unpaired (Function.swap Nat.pair))
```

**Every one is a closure property, and none is settled by reduction.** There is
no boundary equation here in any form — no `f 0 = …`, no `f 1 = …`, no defining
equation quantified or otherwise. Establishing `Nat.Primrec.add` means
exhibiting an actual derivation of addition from the seven constructors, which
is real content at every argument. That is what makes this family unusually
clean for a held-out slot, and it is why ADR-1220 preferred it to
`Factorization.Root`'s 3-of-10.

**Nothing in the drawn ten is a constructor of the inductive being declared**,
checked explicitly and worth checking: a row the construction itself settles
would be spent the moment it landed. The Mathlib inventory carries **14** rows
for this module and none of them is a constructor — Mathlib's `zero`/`succ`/
`left`/`right`/`pair`/`comp`/`prec` are not statement rows. The three rows that
do not make the pool are `brecOn` (needs `Nat.Primrec.below`), `id` (needs `id`)
and `sub` (needs `instSubNat`).

**The pool is 11 against a `PER_FAMILY` of 10, so the slack is ONE row.** That
is the tightest margin any recent draw has had, and it is a real consequence for
whoever authors draw 16: if any single one of the eleven becomes catalogued or
unstatable, the pool is exactly 10 and still works; if two do, `select()` raises
and the whole refill fails. Declaring `id` would add `Nat.Primrec.id` and widen
it, and this lane deliberately did **not** do that — `id` is generic enough to
risk churning other families, and the churn screen's value comes from its being
run against a small, known set of new constants.

## What was declared

`crates/axeyum-lean-kernel/src/nat_prelude/primrec.rs`, wired into
`nat_prelude.rs` after `declare_unpair_all` (which the `left`/`right`
constructors name).

```text
Nat.casesOn.{u} {motive : Nat → Sort u} (t : Nat)
    (zero : motive Nat.zero) (succ : (n : Nat) → motive n.succ) : motive t
  := Nat.rec.{u} motive zero (fun n _ih => succ n) t

inductive Nat.Primrec : (Nat → Nat) → Prop
  | zero  : Nat.Primrec (fun _ => 0)
  | succ  : Nat.Primrec Nat.succ
  | left  : Nat.Primrec Nat.unpairLeft
  | right : Nat.Primrec Nat.unpairRight
  | pair  {f g} : Primrec f → Primrec g → Primrec (fun n => Nat.pair (f n) (g n))
  | comp  {f g} : Primrec f → Primrec g → Primrec (fun n => f (g n))
  | prec  {f g} : Primrec f → Primrec g →
                  Primrec (Nat.unpaired fun z n =>
                    Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n)
```

**No theorem about either is declared, and no fact is registered.**
`Nat.Primrec.add`, `.mul`, `.pow`, `.pred`, `.const` and `.of_eq` are exactly
the ordinary supporting theorems ADR-0653 says land the day after a draw, from
`development`, where they cost nothing. ADR-1220's retrospective on the
`Nat.dist` lane is the reason: declaring seven helpful lemmas alongside a
construction is what spent the family it was opening.

Three choices that are not cosmetic:

- **`Nat.casesOn` is universe-polymorphic because Mathlib's is.** The two rows
  that consume it here instantiate `motive := fun _ => Nat`, so a `Nat`-only
  version would have sufficed for the screen — and it would have been a
  *different construction* from Mathlib's, which is the `Nat.multichoose` side
  of the mirror-flip criterion and would make every statement over it a
  divergent mirror rather than the same proposition.
- **`left`/`right` are Mathlib's `fun n => n.unpair.1`/`.2` with the `Prod`
  removed.** ADR-1220's finding stands and is what made this family reachable:
  "needs `Prod`" is a claim about a TYPE, and splitting the projections makes it
  false. Every `ml430` mirror stated over Mathlib's `Nat.unpair` stays `open`.
- **The function argument is an INDEX, not a parameter** (`num_params = 0`).
  Every constructor concludes at a different function, which is the whole
  content of the predicate. Positivity is immediate — every recursive occurrence
  is a bare `Nat.Primrec f` hypothesis — so the generated recursor is ordinary.

## The part that matters: an inductive `Prop` has no evaluation test

This repository's standing rule is that **the trusted gate cannot tell you a
`Definition` is wrong**: `add_declaration` type-checks a term against its stated
type, and `Nat → Nat` is `Nat → Nat` whatever the body computes. So every
definition here carries an evaluation test at concrete numerals.

`Nat.Primrec` has no value to reduce. A constructor stating a transposed,
weakened or simply wrong closure property type-checks exactly as happily as the
intended one, and `axiom_footprint`, the prelude build and the
environment-derived coverage assertion are all blind to it. **Declaring an
inductive `Prop` means giving that safeguard up**, and doing so silently would
be the checker-that-cannot-fail defect arriving through the door marked "it is a
`Prop`, there is nothing to evaluate".

Three things replace it, in `primrec_tests.rs`. They fail on disjoint defect
classes, which is the point:

### 1. The predicate does not evaluate, but its INDICES do

Each constructor concludes at `Nat.Primrec <a concrete `Nat → Nat` term>`, and
that term is an ordinary function this kernel reduces. So the evaluation test is
**recovered one level in**: `def_eq` the constructor's INFERRED type against
`Nat.Primrec F` for an `F` built in the test, and separately reduce `F` at
numerals against a hand table. Neither link alone is worth much; together they
say the kernel admitted a closure property about a function whose values are
known.

`n = 5` is the discriminator for `left`/`right`, because `unpairLeft 5 = 1` and
`unpairRight 5 = 2` — different on both components, so a swap fails. The two
nullary pairs are additionally asserted to state *different* propositions, which
is the check that a copy-paste between them fails.

**This generalises past `Nat.Primrec`.** Any inductive whose indices are terms
in a computational carrier has this route available. An inductive over an opaque
carrier does not, and would need a different answer.

### 2. Closed derivations, assembled and inferred

`comp succ succ` and `prec zero succ` are built from the real constructor
constants, `Kernel::infer`red, and their conclusions evaluated. This is the
check no per-constructor assertion can make: a set of constructors can each be
individually well-typed against an expectation that is wrong in the same way,
and only chaining them exposes it — the mutually-consistent-errors failure that
`Int.fib_two_mul`'s five backwards `isymm` call sites demonstrated.

`prec zero succ`'s index was **simulated in Python before any Rust was
written**, which is what picked the discriminating arguments:

| m | z = uL m | n = uR m | value | value if the two `Nat.pair`s are TRANSPOSED |
| --- | --- | --- | --- | --- |
| 0 | 0 | 0 | 0 | 0 — agrees, discriminates nothing |
| 1 | 0 | 1 | 1 | 1 — agrees, discriminates nothing |
| 3 | 1 | 1 | **3** | **2** |
| 4 | 0 | 2 | **10** | **13** |
| 5 | 1 | 2 | 102 | 32 |

So `m = 3` and `m = 4` are the controls and `m = 0`/`m = 1` are deliberately
**not** used as controls — a control built on them would pass while measuring
nothing, which is the vacuous-control failure this repository keeps rediscovering.
`m = 5` discriminates too and is avoided: 102 is a 102-deep unary `succ` tower in
this prelude.

### 3. A binder-count assertion per constructor

`zero`/`succ`/`left`/`right` bind 0; `pair`/`comp`/`prec` bind 4 (`{f g}` plus
two `Primrec` premises). A `pair` written with one premise is well-typed and
states something strictly **weaker**, and nothing else in the file would notice —
verified, see the mutation table.

### Mutation results

Run in this lane's own worktree, never the shared checkout.

| mutant | outcome |
| --- | --- |
| `left`/`right` constructors swapped | kills **exactly** `primrec_constructor_indices_are_the_intended_functions` |
| `prec`'s two `Nat.pair`s transposed | kills **exactly** `primrec_closed_derivations_compose_and_their_functions_evaluate` |
| `pair` loses its `hf` premise | kills **exactly** `primrec_constructors_bind_the_arguments_mathlib_binds` |
| `casesOn` minors reordered (succ before zero) | kills **exactly** `cases_on_selects_the_right_branch_and_exposes_the_predecessor` |
| `casesOn`'s succ minor handed the scrutinee rather than the predecessor | kills **all four** — the mutant does not type-check, so `build_nat_prelude` fails and poisons every test in the file |

The fifth is reported as it behaved rather than as a clean kill. It is the
documented one-bad-declaration-poisons-the-prelude effect, and it carries a
finding: **`Nat.casesOn`'s dependent type is tight enough that most wrong
implementations do not type-check at all.** That is genuinely unlike `Nat → Nat`,
where every wrong body is well-typed. The wrong `casesOn` that *does* type-check
is the one with the arguments in the wrong ORDER, and that is what the fourth
mutant tests — Lean's `casesOn` takes the scrutinee first, and getting it
backwards would make every consuming Mathlib statement fail to elaborate while
this kernel accepted it happily.

### One gap this lane found and closed

`every_nat_declaration_is_checked_and_axiom_free` reads the ENVIRONMENT and is
scoped, deliberately and with a documented reason, to `Definition`/`Theorem`
kinds. So it caught `Nat.casesOn` immediately (and was the only thing that did)
and **is structurally blind to the inductive, its seven constructors and its
recursor**. Those are covered by name in
`every_promised_name_is_admitted_with_the_expected_kind`, and all eight names are
now listed there, so a constructor silently dropped from `add_inductive` fails
rather than leaving a weaker predicate nothing checks.

## Post-declaration state

**Environment 2696 → 2706, exactly +10**, and the kind breakdown confirms it
rather than the total alone: `definition 371 → 372` (`casesOn`),
`inductive 24 → 25`, `constructor 31 → 38` (+7), `recursor 24 → 25`.
`axiom=30` unchanged — that is `AxReal` and nothing here touches it.

**Kernel.** `--lib nat_prelude::primrec` 4 passed / 0 failed (nonzero,
confirmed). `--lib nat_prelude::` **303 passed / 0 failed**, up from 302 — the
whole prelude sweep, because one bad declaration poisons the shared build and a
filtered subset cannot see it.

**Snapshot refresh.** `gen-autogenesis-nursery-refill.py --check` regenerates
the manifest **byte-identically** under the refreshed snapshot: 420 entries,
`development=160 held-out=150 train=110`, unchanged. Checked rather than
assumed — ADR-1095's refresh displaced two `train` rows.

| gate | before | after |
| --- | --- | --- |
| `check-autogenesis-nursery.py` | exit 0 | exit 0 |
| `check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS` | `held_out=166 settled=0 PASS` |
| `check-holdout-closed-evaluation.py` | `held_out=166 closed_shaped=0 violations=0 PASS` | same, `snapshot_declarations=2706` |
| `check-holdout-adjacency.py` | 16 families, 0 refused | 16 families, 0 refused |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | exit 0 | exit 0 |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `env=2693` | exit 0, `env=2706` |
| `check-shape-duplicates.py` | — | exit 0, 15 groups, all allowlisted |
| `validate-facts.py` | — | exit 0 |

**Layout RP through the real machinery, against the committed post-declaration
snapshot**, with index 3's `Nat.ceilRoot`/`Nat.floorRoot` simulated (they are not
this lane's to declare):

```text
[0] natural-primitive-recursion   held-out     Mathlib.Computability.Primrec.Basic
[1] natural-fibonacci-basic       development  Mathlib.Data.Int.Fib.Basic
[2] natural-prime-divisibility    train        Mathlib.Data.Int.NatPrime
[3] natural-integer-root          held-out     Mathlib.Data.Nat.Factorization.Root
    new entries 40 (held-out 20)
    R12: PASS
    R11 natural-integer-root          clean  topic=0 vocab=0/10
    R11 natural-primitive-recursion   clean  topic=0 vocab=0/10
    guard(): REFUSED -> R11 ... disclosure ...
```

`Mathlib.Computability.*` sorts before every `Mathlib.Data.*`, so the family
lands at index 0 by sort order rather than by arrangement. R1–R10 and R12 all
pass. **The only remaining refusal is R11's authorable disclosure**, which is a
review that must be PERFORMED and not asserted, and belongs to the draw lane —
two prior lanes correctly refused to write it and so does this one.

The control discriminates: with the constructions removed from the environment,
`select()` refuses with `family 'natural-primitive-recursion' yields 0 screened
candidates, fewer than the 10 the refill takes`.

**Blind-evaluation integrity.** No fact moved partition, no fact was registered,
`nursery-v1.json` was never touched, and no `FAMILY_MODULES`/`FAMILY_ROUTES`
edit is committed — that is the draw lane's edit.

## Decision

**Declare `Nat.casesOn` and the inductive `Nat.Primrec` — construction only —
and author no draw.** Index 0 is filled.

## Consequences

- **Draw 16 needs one more construction and then a review.** Index 0 is done;
  index 3 wants `Nat.ceilRoot`/`Nat.floorRoot`, whose 3-of-10 boundary count
  ADR-1220 measured **against Mathlib's `Finsupp` definition, which we cannot
  build**. That count must be re-measured against whatever construction is
  actually written — plausibly a bounded least-witness search, under which
  `ceilRoot 1 a = a` becomes a real theorem rather than `refl` and the count
  drops. And that route reds `check-holdout-adjacency.py` until draw 11's
  `natural-nth-root` review is redone; that re-review is real work and the same
  lane should do it.

- **The pool is 11 against a floor of 10, and a draw lane should know that.**
  One row of slack. Nothing needs doing today, but if a future lane declares
  `id` or a `Sub Nat` instance, `Nat.Primrec.id`/`.sub` join the pool and the
  drawn ten CHANGES — which, once this family is frozen, is exactly the
  frozen-family churn ADR-1220 introduced the screen for. Run it.

- **The evaluation-test substitute for an inductive `Prop` is reusable, and its
  precondition is worth stating.** "Recover the evaluation test one level in, on
  the indices" works whenever the inductive's indices are terms in a
  computational carrier. `Nat.Primrec`, `Nat.le`, `Nat.Fin` and
  `CReal.UniformlyContinuousOn` all qualify. An inductive over an opaque carrier
  does not, and the next lane in that position needs a different answer rather
  than this one applied by analogy.

- **`every_nat_declaration_is_checked_and_axiom_free` does not see inductives**,
  by design and with a good reason (an `Inductive`/`Constructor`/`Recursor` has
  no proof term for `axiom_footprint` to inspect). The compensating check is a
  by-name list in a different test, which is exactly the hand-maintained shape
  the environment-derived assertion exists to replace. Nobody should read
  "every Nat declaration is checked" as covering the inductive machinery; today
  it is covered because eight names were added by hand, and a ninth added later
  would not be.

- **ADR-1220's two new screens both stayed clean here, and both were re-run
  rather than inherited.** That is the point of the entry: they are cheap, they
  are pure Python against machinery that already exists, and each of them
  changed a decision in ADR-1220. Neither changed one here — which is the
  outcome you want and is not the outcome you can assume.
