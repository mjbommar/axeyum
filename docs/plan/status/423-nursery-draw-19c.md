# Lane: nursery-draw-19c — draw 19 is authored, and the deferral nobody enforced was the whole refusal

<!-- plan-section: lane-status -->

**Done (`DONE`, nursery-draw-19c, 2026-09-02).** Draw 19 is **authored** after
two refusals (ADR-1420 for draw 17's shape, ADR-1556 for this draw). Four
families, 40 rows: `discrete-step-and-counting-bounds` (held-out),
`natural-bit-constructor` (development), `natural-binomial-bounds` (train),
`power-and-square-decompositions` (held-out).
`check-dispatchable-frontier.py` goes from **2 to 22** against a floor of 10 and
its exit status from **1 to 0**. Decision:
[ADR-1561](../../research/09-decisions/adr-1561-draw-19-is-authored-and-draw-10s-deferral-was-the-whole-refusal.md).

## Gates, before and after (each run bare, exit captured before any `grep`)

| gate | before | after | headline (after) |
| --- | ---: | ---: | --- |
| `gen-autogenesis-nursery-refill.py --check` | 0 | 0 | `entries=540 env=3018 development=190 held-out=210 train=140 screen_drift=31` |
| `check-autogenesis-holdout-isolation.py` | 0 | 0 | `held_out=226 files_scanned=1114 references=0 PASS` |
| `check-holdout-adjacency.py` | 0 | 0 | **22** held-out families, **0 refused**, 4 undisclosed (advisory) |
| `check-draw7-frozen-families.py` | 0 | 0 | `frozen=50 moved=0 new=4 control=FIRES PASS` |
| `check-partition-edges.py --baseline` | 0 | 0 | `drawn=756 crossing=198 baselined=198 violations=0 PASS` |
| `check-holdout-closed-evaluation.py` | 0 | 0 | `held_out=226 closed_shaped=0 violations=0 PASS` |
| `check-autogenesis-already-proved.py` | 0 | 0 | name-match report only, no new match |
| `validate-facts.py` | 0 | 0 | 2632 → **2672** facts, 0 errors (`open` 226 → 266) |
| `frontier-shape-census.py` | 0 | 0 | primary population 24 → **43**, targetable **4 → 23** |
| `check-autogenesis-nursery.py` | **1** | **1** | output **byte-identical** before/after |
| `check-development-partition.py` | **1** | **1** | output **byte-identical** before/after |
| `check-dispatchable-frontier.py` | **1** | **0** | G7 clears: **2 → 22** dispatchable, floor 10 |
| `adr-1561-draw-19-screen.py` | — | 0 | `families=4 held_out=2 pairs_with_draw10_modules=40 pairs_without=0 coherent_bundles=3 coherent_pairs=0 failures=0` |
| `check-links.sh` | — | 0 | all links ok |
| `gen-adr-index.py` | — | 0 | `rows=777` |

Every contamination-measuring gate was green at start, so the STOP condition did
not fire. The two component gates did not worsen — their output is
**byte-identical** before and after, which is the prediction ADR-1556 made and
the reason a draw cannot move them: a fresh row carries `depends_on: []`, which
is exactly what those two read. `partition-edges` holds at `violations=0` with
the baseline **unchanged at 198** while `drawn` goes 716 → 756.

## The finding: the deferral nobody enforced was the entire refusal

ADR-1559 opened `Mathlib.NumberTheory.{PrimeCounting,Chebyshev}` and the ADR-1556
screen went to `viable=196 disjoint_pairs=219`. That was **not** sufficient. Of
the 40 module-disjoint pairs of clean held-out bundles this lane enumerated, every
single one uses `Mathlib.NumberTheory.SumTwoSquares` **and**
`Mathlib.NumberTheory.PythagoreanTriples` — the two modules draw 10 deferred in a
generator comment that ADR-1556 measured is read by no guard, and explicitly left
for the next lane to own.

Measured with the real `screen_family` / `barred_modules` /
`is_closed_evaluation` over every module subset of the unowned pool up to six
modules:

| what is withheld | clean held-out bundles | module-disjoint pairs |
| --- | ---: | ---: |
| nothing | 168 | **40** |
| `PythagoreanTriples` alone | 58 | **0** |
| `SumTwoSquares` alone | 146 | **0** |
| both | 47 | **0** |

Withholding **either one on its own** makes R5 unsatisfiable. So the deferral is
not a preference costing slack; honouring it means refusing draw 19 a third time.
Its stated reason does not survive measurement: `Int.sq_ne_two_mod_four`
(`∀ z : ℤ, z * z % 4 ≠ 2`) was called adjacent to the TRAIN family
`integer-modular-equivalence`, whose entire published subject vocabulary is the
single constant `Int.ModEq` — which that row does not mention, being about `%` —
and none of that family's 20 rows is about a square. `Nat.sq_add_sq_mul`
(Brahmagupta–Fibonacci) was named in the same sentence with no reason given at
all. Both rows use **zero** constants any development or train family publishes:
by the enforced measure they are among the least adjacent rows in the pool. The
judgement is now written where a guard reads it — the
`power-and-square-decompositions` review row — and the screen asserts the table
above, so a future lane that disagrees has to move a number.

## The second finding: R11 makes a topically coherent held-out family impossible

The first draft of this draw tried the obvious construction — one
`Mathlib.NumberTheory.*` family and one `Mathlib.Data.Nat.Factorization.*`
family. **Both are refused, and so is every topically tight bundle in the pool**,
by R11's vocabulary rule (at most 5 of 10 rows about a constant a
development/train family publishes):

| bundle | refusal |
| --- | --- |
| `Choose.{Bounds,Dvd,Sum}` | topic `Choose` (`natural-binomial`, `natural-factorial-choose-and-squarefree`), vocabulary **10/10** |
| `{BinaryRec, Bitwise}` | topic `Bitwise` (`natural-bitwise`, `natural-bitwise-basics`), vocabulary **9/10** |
| `Factorization.{Basic,Induction,PrimePow}` + `Multiplicity` | vocabulary **9/10** |
| `NumberTheory.{Chebyshev,PowModTotient,PrimeCounting,PrimesCongruentOne}` | vocabulary **6/10** |

Requiring two shared leading path segments leaves **3 clean bundles of 168 and no
two of them module-disjoint**, so R5 cannot be met from coherent families at all.
A held-out family here is cross-topic **by construction** — the draw-10 precedent
(`descent-and-well-ordering` = LeastGreatest + SumFourSquares +
Order.Interval.Finset.Nat), not a departure. The same measurement chooses the
dispatchable families: `natural-bit-constructor` and `natural-binomial-bounds`
are refused *for held-out* on topic, which is R11 saying a lane already works that
mathematics, and they add no new adjacency — `Nat.bit` already carries 19 kernel
theorems and `Nat.choose` is already published by `natural-binomial`.

**`Mathlib.Data.Nat.Count` (22 rows, R11-clean, the largest block in the window)
was deliberately not taken**, and this is a judgement no guard makes. It is
barred from held-out by ADR-1450; as development or train it would sit beside
`discrete-step-and-counting-bounds`, whose five prime-counting rows are
monotonicity and step bounds for a counting function — `count_monotone`,
`count_le`, `count_succ` are the same lemmas one carrier down. R11 cannot see it:
`Nat.count` and `Nat.primeCounting` are different constants, `Count` and
`PrimeCounting` different topic segments.

## The third finding: the R11 stem sweep could not reach this family's adjacency

`power-and-square-decompositions`'s environment sweep is
`[[lcm, Nat.coprime_lcm_eq_mul, 21], [lcmupto, Nat.lcmUpto, 1], [upto, Nat.lcmUpto, 1]]`.
Those stems close the three `lcmUpto` rows and **structurally cannot reach** the
seven prime-power rows — clean because it is not looking, the ADR-1450 shape on a
new family. Screened by shape instead, two real adjacencies exist and are
disclosed in the review rather than dismissed:
`Nat.pow_two_or_has_odd_factor` (`n ≠ 0 → (∃ m, n = 2^m) ∨ (∃ e t, n = e(2t+1) ∧ t ≠ 0)`)
is **strictly weaker** than the drawn `Nat.exists_eq_two_pow_mul_odd` — its second
disjunct gives *some* odd factor, not the 2-adic split; and `Nat.prod_factorization`
(`0 < n → prod (factorization n) = n`) with `Nat.factorization_prime` gives a
factorization multiset but states no drawn row, none of which mentions
`Nat.factorization`. `Nat.divMaxPow`, which computes exactly the p-adic cofactor,
carries **no theorem at all** and its family is itself held-out — blind beside
blind.

## Blindness screen (all 20 held-out rows, before preregistration)

`shape_search` rebuilt through `scripts/cargo-serialized.sh`; freshness confirmed
against `--name Int.quadraticReciprocity --kind theorem --expect 1` → `FOUND 1`,
over an index of **3,041** declarations (`theorem=2458 ns Nat=1084`) — the
control the brief named, landed the same day.

* `--const Nat.primeCounting --kind theorem --expect-absent` and the primed name:
  **ABSENT**; `--name-like primecounting` returns exactly the two DEFINITIONS.
  Closes five rows.
* `--const Nat.lcmUpto --kind theorem --expect-absent`: **ABSENT**;
  `--name-like lcmupto` returns one match, the DEFINITION. Closes three rows.
* `--const Int.le --const Not` (3), `--const Int.lt --const Int.le` (15): neither
  discreteness row; nearest is `Rat.int_one_le_of_pos` (`0 < x → 1 ≤ x`), the
  `a = 0` instance in one direction. The ADR-1556 question was asked and
  answered by reading the declaration: **`Int.lt` is a four-case definition over
  `Nat.lt`** (`int_prelude/defs.rs:declare_order_definitions`), NOT
  `Int.le (a+1) b`, so neither row is `rfl` here.
* `--const Int.Even` (5): all parity characterizations, no order statement.
* `--const Nat.gcd --const Exists` (3), `--const Nat.pred` (14): no
  representability threshold.
* `--const Int.emod` (18), `--const Int.emod --const Int.mul` (6): every
  mod-arithmetic statement here is mod **2**, none about a square.
* `--const Nat.pow --const Nat.dvd` (26), `--const Nat.pow --const Exists` (4),
  `--const Nat.gcd --const Nat.pow` (1), `--const Nat.factorial --const Nat.dvd`
  (6): no perfect-power recognition, no p-adic split, nothing relating a range
  lcm to a factorial.
* Pickaxe: `git log -S <name> --diff-merges=first-parent -- crates/` finds
  **ZERO** commits introducing any of the 19 names, positive control
  `Nat.lcmUpto` = 2 commits. (A plain pickaxe skips merge commits; `--oneline`
  alone prints the whole merge diff, so `-s` is required to read the count.)

## Partition split against policy

`PARTITION_CYCLE` is `(held-out, development, train)` restarting per draw, so a
four-family draw is **2 held-out / 1 development / 1 train** and R5's two-held-out
minimum is met exactly. Derived by `assign_partitions()` from the lexicographic
order of each family's primary module, asserted by the screen against the
preregistered claim, and every tuple is in plain alphabetical order so "first
element" is not a free parameter. Manifest totals move 500 → 540: development
180 → 190, held-out 190 → 210, train 130 → 140 (39% / 35% / 26%).

**Zero churn over the 500 already-drawn rows** — 0 missing, 0 changed, 0
partitions moved — with a working negative control in the same script: flipping
one existing row's partition in a copy IS detected (`changed=1
partitions_moved=1`).

## Did not run

`cargo test`, `cargo clippy`, `just check`, `scripts/check.sh` — no `.rs` file
was touched; the only `cargo` invocation was
`scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example
shape_search` for the blindness screen. `propose-nursery-refill.py` was not run:
it screens by module only and has neither the fact ledger nor
`HELD_OUT_CONSTRUCTIONS` nor the R5 screen, so it is not the candidate space this
lane needed. The environment snapshot was **not** refreshed — `--check` is green
at `env=3018`, the count `heldout-construction-1` refreshed it to this morning.

## What the next lane needs

The pool is thin after this draw: of the 25 unowned modules carrying a screened
row, draw 19 takes 12, and what remains is mostly single-row modules plus the
22-row `Count` block that is now doubly constrained (barred for held-out by
ADR-1450, and withheld from development/train by this lane's judgement while
`discrete-step-and-counting-bounds` is blind). Draw 20 will need another ADR-1420
Route 1 construction, and ADR-1559's shape — Definitions with **no theorem about
them** — is the one that works.

<!-- plan-section: landed-changes -->

| 2026-09-02 | nursery-draw-19c | draw 19 **AUTHORED** after two refusals: `discrete-step-and-counting-bounds` (held-out), `natural-bit-constructor` (development), `natural-binomial-bounds` (train), `power-and-square-decompositions` (held-out); manifest 500 → 540 entries, `check-dispatchable-frontier.py` exit **1 → 0** and **2 → 22** dispatchable against a floor of 10 (ADR-1561) |
| 2026-09-02 | nursery-draw-19c | found: draw 10's unenforced do-not-draw-held-out deferral of `Mathlib.NumberTheory.{SumTwoSquares,PythagoreanTriples}` was **the entire refusal**, not a preference — withholding BOTH gives 0 module-disjoint pairs and withholding **either one alone** also gives 0, against 40 with both available; its stated adjacency (`Int.sq_ne_two_mod_four` beside the train family `integer-modular-equivalence`) does not survive measurement — that family's whole published vocabulary is `Int.ModEq`, which the row does not mention, and neither row uses ANY dev/train-published constant. Overturned, and recorded where a guard reads it |
| 2026-09-02 | nursery-draw-19c | found: R11's vocabulary rule makes a **topically coherent held-out family structurally impossible** in this pool — requiring two shared leading path segments leaves 3 clean bundles of 168 with **0 module-disjoint pairs**; `Choose.*` runs 10/10, `{BinaryRec,Bitwise}` 9/10, `Factorization.*+Multiplicity` 9/10, all of `NumberTheory.*` 6/10. A held-out family here is cross-topic by construction, which is also what selects the two dispatchable families |
| 2026-09-02 | nursery-draw-19c | found: the R11 stem sweep for `power-and-square-decompositions` names only `lcm` stems and **cannot reach** the prime-power machinery 7 of its 10 rows are about — the ADR-1450 shape. Found by shape instead and disclosed: `Nat.pow_two_or_has_odd_factor` is strictly weaker than the drawn 2-adic split, and `Nat.prod_factorization` gives a factorization multiset that states no drawn row |
| 2026-09-02 | nursery-draw-19c | judgement no guard makes: `Mathlib.Data.Nat.Count` (22 rows, R11-clean, the largest block in the window) is **withheld from development and train** while `discrete-step-and-counting-bounds` is blind — `count_monotone`/`count_le`/`count_succ` are `monotone_primeCounting`/`primeCounting_add_le` one carrier down, and R11 sees neither the constant nor the topic overlap |
| 2026-09-02 | nursery-draw-19c | `adr-1561-draw-19-screen.py`: exit 0, `failures=0`, four controls that each must come out the other way and do (the definitional-row check FIRES on a ten built to contain one; the disjointness search finds 1,388 pairs with ADR-1450's `Nat.Count` bar lifted; R11 REFUSES a family scored against a topic twin). Its own first draft asserted ZERO coherent bundles and was wrong — measured at the wrong module cap — which is recorded in the file |
| 2026-09-02 | nursery-draw-19c | gates: every contamination gate green before and after, both component gates **byte-identical**, `partition-edges` `violations=0` with the baseline unchanged at 198 while `drawn` goes 716 → 756, `validate-facts.py` 2632 → 2672 facts / 0 errors, census targetable **4 → 23**, zero churn over the 500 already-drawn rows with a firing negative control |
