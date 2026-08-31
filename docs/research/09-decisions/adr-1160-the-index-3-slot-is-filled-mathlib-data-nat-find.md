# ADR-1160: The index-3 slot is filled — `Mathlib.Data.Nat.Find`, and the pool check has to be a reading as well as a run

Status: accepted
Date: 2026-08-31
Index-summary: Four draws declined in a row on one constraint — cycle index 3
is a held-out slot and nothing late-sorting, topically fresh and
reduction-blind was available to sit in it. This lane screened NINE
late-sorting candidates against the real
`select()`/`assign_partitions()`/`screen_family()`/`is_closed_evaluation`,
with each candidate's constructions simulated into the environment BEFORE any
of them was declared, and found four that pass every hard signal.
`Mathlib.Data.Nat.Find` was chosen and its two constructions declared —
`DecidablePred` (logic prelude, Mathlib's definition verbatim) and
`Nat.findGreatest` (Mathlib's structural recursion, witness explicit,
`Decidable.byCases` for `ite`) — construction only per ADR-0653, with a
six-test discriminating evaluation suite. Post-declaration re-screen against
the REAL environment (2625 declarations): pool 15 rows, R5/R9/R12 pass, R11
topic and vocabulary clean on both held-out families, in TWO independent
4-family layouts; the only remaining refusal in each is R11's authorable
disclosure, which is the draw lane's job. Two findings beyond the family: the
ADR-1115 check **cannot be only a run of the classifier**, because a
`∀`-quantified defining equation is settled by reduction and invisible to
`_ground_shape`; and the candidate space was much larger than the three
constructions ADR-1100 named, because a module can be opened by fewer
constants than its full row set needs. Held-out isolation `held_out=146
settled=0 PASS` before and after; nothing moved partition and no fact was
registered.

Related: ADR-1115 (draw 14 declined; widened `is_closed_evaluation` to see
ground predicates, and named the pre-declaration check this ADR applies),
ADR-1100 (the positional framing, and the three index-3 candidates this lane
re-measured), ADR-1095 (the `ceil(n/3)` mechanism), ADR-0653 (an unblocking
lane declares the construction and nothing else), ADR-0695/ADR-0950 (R12),
ADR-0768 (R11 and its disclosure review), ADR-0542 (the amendment ledger)

## What this lane was asked to do

Make a fifth draw possible: find or build a family that can sit at cycle
index 3 — late-sorting by first Mathlib module name, topically fresh, and
passing ADR-1115's pre-declaration closed-evaluation check. Not to author the
draw; ADR-1100's division of labour stands.

## Everything inherited was re-measured, and one number has moved

Rebuilt `shape_search --release` in this worktree rather than trusting the
prebuilt binary (the documented stale-index hazard, where an ABSENT verdict is
the expensive one). Session start: **2623** declarations against the committed
snapshot's 2593, so the environment HAD moved since ADR-1115 — 30 declarations
from other lanes, none of them this lane's.

Against that tree, with the real `select()`:

- `check-dispatchable-frontier.py` reads `FAIL: G7 queue-below-floor: 6
  dispatchable mirror(s), floor 10` — unchanged from the brief.
- ADR-1115's positional search reproduces exactly. Seven un-owned modules sort
  strictly after `Mathlib.NumberTheory.FactorisationProperties`, totalling 14
  rows (`PowModTotient` 4, `PrimeCounting` 2, `PrimesCongruentOne` 1,
  `PythagoreanTriples` 1, `SumTwoSquares` 1, `RingTheory.Int.Basic` 3,
  `Tactic.IntervalCases` 2), and its layout C — the combination of all seven
  at index 3 — is refused by the real `guard()` with the identical message:

      natural-late-number-theory: vocabulary: 7 of 10 rows are about
        constants a development/train family publishes (allowance 5) --
        Nat.Prime, Nat.Coprime, Nat.totient, Int.gcd

- The count of un-owned modules with at least one screened candidate is **39**
  today where ADR-1115 recorded 38. The environment grew between the two
  measurements; the 38 was accurate when written.
- The three free families reproduce, and so does the control: with
  `natural-avg-pair`, `natural-minmax` and `natural-stirling-numbers` alone,
  the real guard still refuses with `R5 the refill adds 1 held-out families`.

`propose-nursery-refill.py` was not used as a candidate space. It overcounts
(it mirrors only the hygiene screen) and — the point ADR-1100 makes and this
lane depended on — it also UNDERCOUNTS, because it screens per module and says
nothing about what a module would yield if a construction existed.

## What the search actually is, and why it was bigger than expected

ADR-1100 named three index-3 candidates still needing constructions
(`Factorization.Root`, `Find`, `MaxPowDiv`) and ADR-1115 carried them forward.
That list is a subset, not the space.

The right query is: for every un-owned module sorting after the index-2
family, what is the SMALLEST set of currently-inadmissible constants whose
declaration lifts the module's pool to `PER_FAMILY = 10`? Computed
exhaustively over all 1-, 2- and 3-element subsets of each module's ten
most-frequent missing constants, against the real screen. That surfaces nine
candidates, four of them not on ADR-1100's list.

Each was then run through the real `select()`, `assign_partitions()`,
`screen_family()` (with `require_disclosure=False`, so the authorable step
does not mask the hard ones) and `is_closed_evaluation`, with the candidate's
constructions injected into `env` — the pre-declaration check ADR-1115
prescribes, applied to every candidate before a line of Rust was written:

| candidate module | constructions | pool | R9 | R12 | R11 topic/vocab |
| --- | --- | --- | --- | --- | --- |
| `Mathlib.Data.Nat.Find` | `DecidablePred` + `Nat.findGreatest` | 15 | 0/10 | **PASS** | **clean** |
| `Mathlib.Data.Nat.Factorization.Root` | `Nat.ceilRoot` + `Nat.floorRoot` | 18 | 0/10 | **PASS** | **clean** |
| `Mathlib.Data.Nat.MaxPowDiv` | `Nat.divMaxPow` + `padicValNat` | 10 | 0/10 | **PASS** | **clean** |
| `Mathlib.Data.Nat.Factorization.LCM` | `factorizationLCMLeft`/`Right` | 10 | 0/10 | **PASS** | clean (vocab 2/10) |
| `Mathlib.Data.Nat.Choose.Central` | `Nat.centralBinom` | 14 | 0/10 | FAIL `centralBinom 0 = 1` | refused: topic `Choose` |
| `Mathlib.Data.Int.Bitwise` | `Int.bit`/`bodd`/`bitwise` | 10 | 0/10 | FAIL `Int.bit false 0 = 0` | refused: topic `Bitwise` |
| `Mathlib.NumberTheory.PrimeCounting` | `Nat.primeCounting`(`'`) | 12 | 0/10 | FAIL `primeCounting 1 = 0` | clean (vocab 4/10) |
| `Mathlib.Data.Nat.Fib.Zeckendorf` | `Nat.greatestFib` | 11 | 0/10 | PASS | refused: topic `Fib`, vocab 6/10 |
| `Mathlib.Data.Nat.Count` | `Nat.count` + `DecidablePred` | 22 | 0/10 | PASS | clean — and NOT viable, see below |

The three R12 failures are worth naming, because each is exactly the shape
ADR-1115 was written about and each was caught **before** the construction
existed, which is the whole point of the widened classifier: a module whose
pool contains a worked numeric example spends that row the moment its constant
is declared.

`Mathlib.Data.Nat.Count` screens clean here too, on all four signals, and is
still not viable — `Nat.countRange` already proves five of its rows under other
names (ADR-1100). Carried forward as a REFUSAL, not re-verified, and not used.
That is R11's documented shape-2 blindness, and its persistence through a
second independent screen is the argument for the disclosure review existing at
all.

## Why `Find` rather than the other three that pass

All four passing candidates clear the gates. `Find` was chosen on the ONE
question the gates cannot ask, and it is the question ADR-1115 exists to raise.

R12 classifies a statement as reduction-settled only if it is binder-free.
A defining equation stated as `∀ {P} [DecidablePred P], f P 0 = 0` carries
binders, so `_ground_shape` rejects it and the gate reports it clean — while a
natural definition settles it by `Eq.refl` at a free variable. **The
pre-declaration check therefore has to be a READING of the drawn ten as well
as a run of the classifier.** Reading them:

- `Factorization.Root` draws `ceilRoot_one_left : Nat.ceilRoot 1 a = a`,
  `ceilRoot_zero_left : Nat.ceilRoot 0 a = 0` and `ceilRoot_zero_right :
  n.ceilRoot 0 = 0` — three of ten, every one a boundary row that any
  definition special-casing `n = 0` and `n = 1` settles by reduction.
- `MaxPowDiv` draws six such rows of ten (`divMaxPow_{zero,one}_{left,right}`,
  `maxPowDiv.zero`, `maxPowDiv.zero_base`).
- `Factorization.LCM` draws four, and its definition needs a product over prime
  factors, which this kernel cannot state (no `Finset`).
- **`Find` draws none.** Its ten are `findGreatest_eq`, `_eq_iff`,
  `_eq_zero_iff`, `_is_greatest`, `_le`, `_mono`, `_mono_left`, `_mono_right`,
  `_of_ne_zero`, `_of_not` — all with real content, none refl-provable against
  this definition, because `dp (succ m)` is a variable applied to a term so the
  `Decidable.byCases` never ι-reduces at a symbolic argument.

**The disclosure that goes with that, stated here rather than left to be
found:** the pool's rows 12 and 13 ARE this definition's own two equations,
`Nat.findGreatest_succ` and `Nat.findGreatest_zero`, and both would be settled
by reduction. They fall outside the drawn ten **by the alphabet alone**. No
module was added or removed to put them there — that is the move ADR-1115 rules
out on principle, and it was not made. A draw lane that COMBINES
`Mathlib.Data.Nat.Find` with another module changes which ten are drawn and
must re-run the screen; a family over this module alone is what was measured.

## Decision

**Declare two definitions, construction only (ADR-0653), and no theorem about
either.**

### `DecidablePred.{u}` — in the LOGIC prelude

`crates/axeyum-lean-kernel/src/prelude.rs`, beside `Decidable`:

```text
DecidablePred.{u} : Π (α : Sort u) (p : α → Prop), Sort (max u 1)
DecidablePred.{u} := fun α p => Π (a : α), Decidable (p a)
```

Mathlib's own definition (`abbrev DecidablePred {α : Sort u} (p : α → Prop) :=
∀ a, Decidable (p a)`), with `α` explicit because this kernel has no instance
implicits. This is not a substitute for Mathlib's; it is the same one, and it
is the vocabulary a Mathlib statement quantifying over a decidable predicate
needs before it can be STATED here at all. Nothing named `DecidablePred`
existed in the environment; checked against the dump before choosing the name,
because a prelude can declare into another prelude's namespace and a collision
surfaces only when a downstream prelude builds.

It goes in the logic prelude rather than in `nat_prelude`, where its only
consumer lives, for a reason worth recording:
`every_nat_declaration_is_checked_and_axiom_free` filters
`kernel.environment()` on the `Nat.` prefix, so a root-level name declared from
`nat_prelude` would be invisible to the one assertion in that file that reads
coverage from the environment rather than from a list. In the logic prelude it
is covered by `double_negation_and_decidable_are_present_and_axiom_free`, which
asserts presence and an empty `axiom_footprint`.

### `Nat.findGreatest` — the index-3 construction

`crates/axeyum-lean-kernel/src/nat_prelude/find_greatest.rs`:

```text
Nat.findGreatest : Π (P : Nat → Prop), DecidablePred Nat P → Nat → Nat
  := fun P dp n => Nat.rec.{1} (motive := fun _ => Nat) 0
       (fun m ih => Decidable.byCases.{1} (P (succ m)) Nat (dp (succ m))
                      (fun _ => succ m) (fun _ => ih))
       n
```

Mathlib's structural recursion, with two surface differences forced by this
kernel rather than chosen: the `DecidablePred` witness is explicit, and the
branch is `Decidable.byCases.{1}` because this kernel declares no `ite` (`ite`
IS `byCases` with constant branches). Per the mirror-flip criterion this is the
`Nat.nth`/`Nat.minFac` case and not the `Nat.descFactorial_of_lt` case — the
bodies agree extensionally, the TYPES differ — so every `ml430` mirror against
Mathlib's `Nat.findGreatest` stays `open`, and a theorem about ours would need
its own `F:nat-*` fact.

**No theorem about either is declared, and no fact is registered.** ADR-0653,
and the precedent of every prior unblocking lane: `Nat.avg`/`Nat.pair`,
`Nat.Abundant`/`Nat.Deficient` and the Stirling pair registered no facts
either.

## The evaluation suite, and why it is not decoration

The kernel cannot tell a `Definition` is wrong. `Π (P : Nat → Prop),
DecidablePred Nat P → Nat → Nat` is that type whatever the body computes, so
`add_declaration` accepts a swapped `byCases` pair, a predicate tested at the
wrong argument, or a wrong base case exactly as happily as the intended
recursion.

Six tests in `find_greatest_tests.rs`, all `def_eq` at concrete arguments
against independently computed values, every one paired with a negative control
naming the specific wrong definition it rules out:

| test | value | rules out |
| --- | --- | --- |
| `DecidablePred` unfolds to a `Pi` over `Decidable` | — | a definition whose codomain does not depend on the bound argument |
| `findGreatest (· = 2) 5 = 2` | 2 | `5` (branches swapped), `3` (tests `P m`, not `P (m+1)`), `0` (never returns `succ m`) |
| `findGreatest (· = 2) 2 = 2` | 2 | a definition that never returns its own argument |
| `findGreatest (· = 2) 1 = 0` | 0 | a definition that returns the bound when nothing matches |
| `findGreatest (· = 0) 0 = 0`, and `= 0` at bound 3 | 0 | a base case that consults `P 0` |
| `findGreatest (· ≤ 3) 6 = 3` | 3 | `6` (returned the bound), `0` (returned the smallest) |

The predicate is true at exactly one point in four of the six, which is what
makes the discriminators bite — an always-true or always-false predicate makes
every one of those bugs invisible. The last test uses a predicate true at four
points, because with a single witness "largest" and "any" coincide. All
magnitudes are single digits: this prelude's numerals are unary towers, so the
binary literal fast path never fires and a large argument would cost more than
the whole prelude.

The `DecidablePred` witnesses go through `Decidable.ofBool` on `Nat.beq` /
`Nat.ble`, with the negative direction by contraposition — the same shape
`rat_prelude/decidable.rs` uses for `Rat.decidable_le`. The fixture asserts its
own witness types as `DecidablePred Nat P` before use, so a later `def_eq`
failure cannot be misread as a `findGreatest` bug.

## Verification

Every number below is from the real machinery, run in this worktree.

**Kernel.** `cargo test -p axeyum-lean-kernel --lib find_greatest` is 6 passed
/ 0 failed (nonzero, confirmed). `--lib nat_prelude::` is **284 passed / 0
failed**, up from 278 — the whole prelude sweep, not a filtered subset, because
one bad declaration poisons the shared prelude build. `--lib prelude::` is
**622 passed / 0 failed**. `cargo check --all-targets` clean.
`every_nat_declaration_is_checked_and_axiom_free` reads the ENVIRONMENT and
covers `Nat.findGreatest` via `definition_names`;
`double_negation_and_decidable_are_present_and_axiom_free` covers
`DecidablePred` and asserts an empty `axiom_footprint`.

**Environment.** `shape_search --release` rebuilt after the declarations:
**2625** declarations, exactly +2 over the pre-declaration 2623, both new names
present in the dump. `control: axiom=30` unchanged — that is the `AxReal`
package and nothing here touches it.

**Post-declaration re-screen, against the real environment with nothing
simulated**, two independent layouts:

    layout A                                  layout B
    [0] natural-avg-pair       held-out       [0] natural-avg-pair        held-out
    [1] natural-minmax         development    [1] natural-minmax          development
    [2] natural-stirling-...   train          [2] natural-fib-and-bitwise train
    [3] natural-find-greatest  held-out       [3] natural-find-greatest   held-out

    both:  R5 PASS   R9 PASS (0/10)   R12 PASS (0/10)
           R11 natural-avg-pair       clean, vocabulary 0/10
           R11 natural-find-greatest  clean, vocabulary 0/10

`natural-find-greatest`'s environment sweep is `[('decidable', 'Decidable',
20), ('greatest', 'Int.gcd_greatest', 2), ('decidablepred', 'DecidablePred',
1), ('find', 'Nat.findGreatest', 1)]`. The draw lane records that verbatim in
`holdout-adjacency-review-v1.json` after reading those declarations against the
ten drawn statements. Two things that review should know, flagged here rather
than left to be discovered:

- The `greatest` stem's two hits are `Int.gcd_greatest`, the
  greatest-common-divisor characterization — an unrelated function sharing a
  word, the same false-positive class `natural-square-root`'s accepted review
  names.
- The nearest thing in this kernel to a bounded greatest-satisfying search is
  `Nat.sqrt` / `Nat.nthRoot` ("the greatest `m` with `m^k ≤ n`"), which are
  specific instances and prove none of the ten; `Nat.nth` selects the `n`-th
  ASCENDING witness, not the greatest below a bound; `Nat.countRange` counts.
  Enumerated by name against the dump, because a name-based screen cannot see
  a proof under a different name and this is precisely where
  `Mathlib.Data.Nat.Count` failed.

**The disclosure step is deliberately left open.** ADR-0768: the review must
reproduce the LIVE sweep exactly, which is what makes it a disclosure rather
than a rubber stamp. Writing one asserting diligence this lane did not perform
would be the checker-that-cannot-fail defect with a paper trail.

**Blind-evaluation integrity.**
`AUTOGENESIS_HOLDOUT_ISOLATION|held_out=146|files_scanned=1110|settled=0|
references=0|verdict=PASS` before and after. No fact moved partition, no fact
was registered, `nursery-v1.json` was never touched, and no
`FAMILY_MODULES`/`FAMILY_ROUTES` edit is committed — that is the draw lane's
edit and it cannot pass `guard()` without the disclosure rows.

**Gates.** `check-autogenesis-nursery.py` OK,
`create-autogenesis-nursery-dispatch-baseline.py --check` OK,
`gen-autogenesis-nursery-refill.py --check` OK (`env=2625`),
`check-holdout-closed-evaluation.py` PASS
(`held_out=146 closed_shaped=0 violations=0 snapshot_declarations=2625`).

**The R12 result is not vacuous, checked rather than assumed.** The classifier
in the tree is the widened one: it returns `True` for `Nat.Abundant 12`,
`Nat.Deficient 1` and `Nat.centralBinom 0 = 1`, and `False` for
`Monotone Nat.fermatNumber`. It also returns `False` for
`∀ {P} [DecidablePred P], Nat.findGreatest P 0 = 0` — which is the disclosure
above, measured: the gate would not have caught that row had it been drawn.

**The snapshot refresh churned nothing.** Regenerating
`nursery-v2-extension.json` against the refreshed snapshot produced a
byte-identical manifest — 0 entries dropped, 0 added, 0 moved, no other field
changed, diffed by `fact_id`. Recorded because ADR-1095's own refresh DID
displace two `train` rows, so "a refresh is harmless" is not something to
assume.

## Consequences

- **Draw 15 has two independent 4-family layouts, each one authorable
  disclosure row away from `GUARD PASSED`.** The draw lane authors
  `FAMILY_MODULES`/`FAMILY_ROUTES`, the two R11 reviews
  (`natural-avg-pair`'s is already recorded and live from ADR-1115) and
  regenerates the manifest. This lane enables a draw; it does not author one.

- **The pre-declaration check ADR-1115 prescribes is necessary and not
  sufficient, and this ADR is the first to measure why.** `is_closed_evaluation`
  is binder-free by construction, so a `∀`-quantified DEFINING EQUATION —
  `f P 0 = 0`, `f P (n+1) = …` — is settled by reduction and reports clean.
  Every one of Mathlib's `Nat.*` modules that defines a function carries such
  rows. Run the classifier, and then READ the drawn ten for boundary equations
  your definition will make refl. That reading is what separated `Find` (zero
  such rows in the ten) from `Factorization.Root` (three) and `MaxPowDiv`
  (six), and no gate we have makes the distinction.

- **The index-3 candidate space is larger than the list of named
  constructions.** ADR-1100 and ADR-1115 both carried three candidates forward;
  the real search — minimum construction subsets per module, against the real
  screen — found nine, of which four pass every hard signal and three are new.
  A future unblock should re-run that sweep rather than inherit a list, for the
  same reason this repository keeps rediscovering: a file that records
  obstacles accumulates stale ones by construction.

- **Three remaining index-3 candidates are pre-screened and available** if a
  later draw needs a different one: `Factorization.Root` (18 rows, `Nat.ceilRoot`
  + `Nat.floorRoot`), `MaxPowDiv` (10 rows, `Nat.divMaxPow` + `padicValNat`)
  and `Factorization.LCM` (10 rows). All three pass R9/R11/R12 as the gates
  measure them, and all three draw boundary rows their construction would
  settle, so all three need the reading above before they are used — and
  `Factorization.LCM` additionally needs a product over prime factors this
  kernel cannot state.

- **`DecidablePred` is now available to the whole kernel**, which is a real
  side benefit rather than scaffolding: it is the vocabulary every Mathlib
  statement quantifying over a decidable predicate needs before it can be
  stated here, and `Mathlib.Data.Nat.Count` (22 rows) and the rest of
  `Mathlib.Data.Nat.Find` (`Nat.find`, 15 more rows) are now one construction
  each from being statable. Both are `development`/`train` material, not
  held-out: `Count` for the shape-2 contamination ADR-1100 measured.
