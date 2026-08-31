# ADR-1245: Index 3 is filled — and a boundary count is definition-relative, so an inherited one is a claim about a tree that does not exist

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1220 measured that draw 16 needs two viable held-out slots
(cycle indices 0 and 3) and ADR-1240 filled index 0. This lane fills index 3 by
declaring `Nat.floorRoot` and `Nat.ceilRoot`, construction only (ADR-0653),
opening `Mathlib.Data.Nat.Factorization.Root` at pool **18**. Mathlib's bodies
are products over `Nat.factorization`, a `Finsupp` this kernel has no way to
state, so ours are the extensionally equal **bounded searches** — verified
against the prime-factorisation formula by simulation over 400 `(n, a)` pairs
before any Rust was written, zero mismatches. **ADR-1220's inherited 3-of-10
boundary count was measured against Mathlib's definition and is 1 of 10 against
this one**: `Nat.ceilRoot_one_left` and `Nat.ceilRoot_zero_right` both stop
being `Eq.refl`, exactly as ADR-1220 predicted a search would do, and only
`Nat.ceilRoot_zero_left` remains. That reading is now a **gated assertion at
free variables**, not prose. Draw 11's `natural-nth-root` adjacency review was
**redone** (the two names take the `root` sweep from 11 declarations to 13) and
records the finding that these are DIVISIBILITY roots while `Nat.nthRoot` is an
ORDER root — measured, since substituting `floorRoot` into `Nat.le_nthRoot_iff`
makes it FALSE at `(2, 3, 12)`. Eleven mutants: nine killed, **two survived and
both are reported**, one of them the definition-shaped third outcome (a delta
height below `Nat.pow`/`Nat.mod` — admitted, every value unchanged, invisible to
every test). Environment 2706 -> **2708**, exactly +2. Held-out `166`,
`settled=0`, before and after; no fact moved partition and none was registered.
No draw is authored.

Related: ADR-1240 (index 0, which this completes), ADR-1220 (the two-slot
measurement, the inherited boundary count this corrects, and the two screens),
ADR-1160 (the boundary-equation READING and the first index-3 unblock),
ADR-1230 (the three mutation outcomes), ADR-0925 (nursery draw 11, whose review
is redone here), ADR-0910 (`Nat.nthRoot`), ADR-0768 (R11 and its disclosure
review), ADR-0653 (construction-only unblocks), ADR-0542 (the amendment ledger)

## What was verified before anything was written

`shape_search --release` was rebuilt in this worktree rather than trusted from a
prebuilt binary — the documented stale-index hazard, where a false ABSENT is the
expensive verdict. Session start: **2706** declarations, matching the committed
snapshot exactly, so nothing had landed since ADR-1240.

Against that tree, with the real machinery
(`docs/research/09-decisions/adr-1245-index-three-screen.py`, which loads
`gen-autogenesis-nursery-refill.py`, `check-holdout-adjacency.py` and
`check-holdout-closed-evaluation.py` by path and calls the actual functions —
`propose-nursery-refill.py` is not used as a candidate space, per ADR-1160):

| ADR-1220 claim | reproduced |
| --- | --- |
| pool 18 with `Nat.ceilRoot` + `Nat.floorRoot` | **yes**, 18 |
| pool 0 without them | **yes**, 0 |
| no frozen family's drawn ten churns | **yes**, 0 of 42 families |
| declaring them reds `natural-nth-root`'s recorded review | **yes**, `root` 11 -> 13, message identical |
| R12 clean over the drawn ten | **yes**, 0 of 10 |
| boundary rows in the drawn ten: 3 | **NO — see below.** 1 against the construction actually written |

Two things the brief said, both correct: `check-autogenesis-nursery.py` is
GREEN (it was repaired after ADR-1220 read it red on `main`), and
`check-autogenesis-holdout-isolation.py` reads `held_out=166 settled=0 PASS`.

## The finding: a boundary count belongs to a definition, not to a module

ADR-1160's rule is that the pool check has to be a READING as well as a run of
the classifier, because `is_closed_evaluation` is binder-free by construction: a
`∀`-quantified defining equation is settled by reduction and still reports
clean. ADR-1220 applied that rule to `Factorization.Root` and read **3 of 10**,
correcting a name-based guess of 5.

That reading was right about Mathlib's definition and says nothing about ours,
and ADR-1220 flagged the gap itself: *"the boundary reading is
DEFINITION-RELATIVE and this ADR's count assumes Mathlib's definition… that is
a measurement the building lane must make, not a claim to inherit."*

Made. The drawn ten, printed verbatim from the real `select()`:

```text
[0] Nat.ceilRoot_eq_zero      ∀ {a n : ℕ}, n.ceilRoot a = 0 ↔ n = 0 ∨ a = 0
[1] Nat.ceilRoot_ne_zero      ∀ {a n : ℕ}, n.ceilRoot a ≠ 0 ↔ n ≠ 0 ∧ a ≠ 0
[2] Nat.ceilRoot_one_left     ∀ (a : ℕ), Nat.ceilRoot 1 a = a
[3] Nat.ceilRoot_one_right    ∀ {n : ℕ}, n ≠ 0 → n.ceilRoot 1 = 1
[4] Nat.ceilRoot_pow_self     ∀ {n : ℕ}, n ≠ 0 → ∀ (a : ℕ), n.ceilRoot (a ^ n) = a
[5] Nat.ceilRoot_zero_left    ∀ (a : ℕ), Nat.ceilRoot 0 a = 0
[6] Nat.ceilRoot_zero_right   ∀ (n : ℕ), n.ceilRoot 0 = 0
[7] Nat.dvd_ceilRoot_pow      ∀ {a n : ℕ}, n ≠ 0 → a ∣ n.ceilRoot a ^ n
[8] Nat.dvd_pow_iff_ceilRoot_dvd
                              ∀ {a b n : ℕ}, n ≠ 0 → (a ∣ b ^ n ↔ n.ceilRoot a ∣ b)
[9] Nat.floorRoot_eq_zero     ∀ {a n : ℕ}, n.floorRoot a = 0 ↔ n = 0 ∨ a = 0
```

**Exactly one of them, `[5]`, is settled by reduction against this
construction.** The three ADR-1160 and ADR-1220 named were `ceilRoot_one_left`,
`ceilRoot_zero_left` and `ceilRoot_zero_right`; the first and third move:

- **`[2] ceilRoot_one_left` is a real theorem.** At `n = 1` the guard reduces
  but the search's `Nat.rec` on the fuel `a` does not, so the statement carries
  the content "the least `b ≥ 1` with `a ∣ b` is `a`". ADR-1220 predicted
  precisely this outcome for a bounded-search construction.
- **`[6] ceilRoot_zero_right` is not `refl` either** — the guard is stuck at a
  symbolic `n`. It is a two-case split whose branches are each `refl`, so it is
  *cheap*; it is disclosed as cheap rather than as free.
- **`[5] ceilRoot_zero_left` remains a boundary row** and is disclosed as one.
  The guard is a `Nat.rec` on `n`, and `n = 0` ι-reduces however symbolic `a`
  is.

**No case was written to move a row and none was removed either.** A definition
special-casing `n = 1` would settle `[2]` by reduction; none was written,
because a bounded search has no reason to have one. And exactly ONE of
`zero_left`/`zero_right` is reducible under any ordering of a two-argument
guard — putting the `a = 0` test outermost simply moves the boundary row from
`[5]` to `[6]`, both of which are drawn. A variant that reaches 0 exists (search
`[1, a+1]` instead of `[1, a]`, so neither zero case reduces) and was
deliberately **not** written: an unnatural fuel bound chosen to dodge a
classifier is the move ADR-1115 rules out on principle, arriving from the other
side.

**The reading is now a gated assertion.** `factorization_root_tests::
exactly_one_drawn_row_is_settled_by_reduction` builds each of those five terms
at genuinely FREE variables and asserts `def_eq` for `[5]` and `!def_eq` for
`[2]` and `[6]`, plus both `floorRoot` analogues. Every negative differs in a
SMALL term (a numeral against an fvar, or a stuck `Nat.rec` against `0`), so no
failing `def_eq` here can run away the way ADR-1230's transposed control did;
the whole file runs in 3.7 s. Two mutants kill it (below), so it is not a
check that cannot fail.

## What was declared

`crates/axeyum-lean-kernel/src/nat_prelude/factorization_root.rs`, wired in
after `declare_find_greatest_all`.

Mathlib (`Mathlib/Data/Nat/Factorization/Root.lean`):

```text
def Nat.floorRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ (k / n)
def Nat.ceilRoot (n a : ℕ) : ℕ :=
  if n = 0 ∨ a = 0 then 0 else a.factorization.prod fun p k => p ^ ((k + n - 1) / n)
```

Ours:

```text
Nat.floorRoot n a := match n with
  | 0      => 0
  | succ m => Nat.rec 0 (fun b ih => if a % (b+1) ^ (m+1) == 0 then b+1 else ih) a
Nat.ceilRoot  n a := match n with
  | 0      => 0
  | succ m => (Nat.rec (fun _ => 0)
                       (fun _ g i => if i ^ (m+1) % a == 0 then i else g (i+1)) a) 1
```

`floorRoot` scans `b` DOWN from `a` and takes the first hit, so it returns the
greatest `b` with `b ^ n ∣ a`; `ceilRoot` scans `i` UP from `1` with `a` units
of fuel, so it returns the least `b ≥ 1` with `a ∣ b ^ n`. Both bounds are
sound — `b ^ n ∣ a` forces `b ≤ a` for `a ≠ 0`, and `⌈k/n⌉ ≤ k` for `n ≥ 1`.

Four choices that are not cosmetic:

- **`Nat.factorization` cannot be written here at all**, so this is the
  `Nat.multichoose` side of the mirror-flip criterion rather than the
  `Nat.descFactorial_of_lt` side: structurally different constructions that
  agree extensionally. Every `ml430` mirror stated over Mathlib's
  `ceilRoot`/`floorRoot` stays `open`, and a theorem about ours would need its
  own `F:nat-*` fact.
- **Agreement was established by simulation FIRST**, over every `(n, a)` with
  `n ∈ [0, 4]` and `a ∈ [0, 79]` — 400 pairs computed both ways, zero
  mismatches. That is what a `Definition` gets instead of a proof, and running
  it before writing any Rust is what makes the construction a decision rather
  than a guess.
- **Mathlib's `a = 0` disjunct is dropped, and that is testable.** It is dead
  code here: `floorRoot`'s downward scan over `a = 0` hits its `Nat.rec` base
  case and `ceilRoot`'s upward scan has zero fuel, so both return `0` unaided.
  A guard no input can reach is a branch nothing can test. Both `_zero_right`
  rows still hold; they stop being `Eq.refl`, which is where the boundary count
  partly comes from.
- **`Nat.findGreatest` was available and was not used.** It takes a
  `Prop`-valued predicate with an explicit `DecidablePred` witness, so routing
  `floorRoot` through it needs a decidability proof for divisibility inside a
  definition body. A raw `Nat.rec` over a `Bool` test keeps both definitions
  parallel, fully computational, and free of that obligation.

**No theorem about either is declared, and no fact is registered.**
`floorRoot_pow_dvd`, `pow_dvd_iff_dvd_floorRoot` and the rest are exactly the
ordinary supporting theorems ADR-0653 says land the day after a draw, from
`development`, where they cost nothing. Measured rather than asserted:
`shape_search --const Nat.ceilRoot` and `--const Nat.floorRoot` are both
**ABSENT** at `declarations=2708`, against a working positive control
(`--const Nat.countRange` is FOUND 21).

## The evaluation suite

The kernel cannot tell a `Definition` is wrong: `Nat → Nat → Nat` is that type
whatever the body computes. Six tests, every value taken from the same Python
table that established agreement, chosen for what they DISCRIMINATE:

| instance | value | rules out |
| --- | --- | --- |
| `floorRoot 2 12` | `2` | `12` (branches swapped), `1` (scan reversed), `3` (**the numeric root**) |
| `ceilRoot 2 12` | `6` | `0` (scan from `i = 0`, where `a ∣ 0 ^ n` always), `12` (least/greatest confused), `4` (the numeric root) |
| `floorRoot 3 8`, `ceilRoot 3 8` | `2`, `2` | an off-by-one in either scan, at a perfect cube where the two must agree |
| `floorRoot 0 5` | `0` | a missing `n = 0` guard, which gives `5` |
| `ceilRoot 0 1` | `0` | a missing `n = 0` guard, which gives `1` |
| `ceilRoot 2 1`, `floorRoot 2 1` | `1`, `1` | a fuel bound of `a - 1` |
| `floorRoot 1 5`, `ceilRoot 1 5` | `5`, `5` | a scan bounded by `n` rather than by `a` |

Three properties are load-bearing rather than stylistic:

- **`a = 8` is deliberately not the numeric-root control.** `floorRoot 2 8 = 2`
  and `⌊√8⌋ = 2` agree, so that comparison would pass while measuring nothing.
  `a = 12` separates all three (`2`, `6`, `3`), and `Nat.nthRoot 2 12 = 3` is
  pinned in the same test so the separation cannot be vacuous through a broken
  `nthRoot`.
- **The vacuous control is MEASURED, not avoided.** `ceilRoot 0 5` is `0` with
  or without the `n = 0` guard, because `5 ∤ 1`, so a guard test written at
  `a = 5` would pass against a definition with no guard at all. Rather than
  quietly using `a = 1` instead, the test builds the UNGUARDED scan as a term
  and pins both directions: it gives `1` at `a = 1` (so the guard bites) and
  `0` at `a = 5` (so that control measures nothing). The floor side is the
  mirror image — `floorRoot 0 5` IS discriminating, giving `0` against the
  unguarded `5`.
- **Magnitudes are single- and low-double-digit**, the largest value formed
  anywhere being `8 ^ 3 = 512`: this prelude's numerals are unary towers and the
  binary literal fast path never fires.

## Mutation results

Eleven mutants, run in this lane's own worktree, never the shared checkout.
Each is scoped to ONE of the two declaring functions, so a string appearing in
both is not changed in both by accident.

| mutant | outcome |
| --- | --- |
| M1 `floorRoot` `bool_select_nat` branches swapped | kills 4 of 6 |
| M2 `floorRoot` tests `b` rather than `succ b` | kills 4 of 6 |
| M3 `ceilRoot` scan starts at `i = 0` | kills 4 of 6 |
| M4 `floorRoot`'s `n = 0` guard returns `a` (the unguarded answer) | kills **exactly** `the_n_zero_guard_is_live_and_one_obvious_control_is_vacuous` |
| M5 `floorRoot` scan bounded by `n` rather than by `a` | kills `the_dropped_a_zero_disjunct_is_dead_code`, `the_scan_bound_is_a_not_n` |
| M6 `ceilRoot` exponent `m` rather than `succ m` | kills 3 of 6 |
| M7 `ceilRoot` guard scrutinee `succ n`, so the `n = 0` branch is unreachable | kills `exactly_one_drawn_row_is_settled_by_reduction`, `the_n_zero_guard_is_live…` |
| M8 `ROOT_HEIGHT` 6 -> 1, below `Nat.pow` and `Nat.mod` | **SURVIVED** |
| M9 `ceilRoot` fuel `succ a` rather than `a` | **SURVIVED** |
| M10 `ceilRoot` guard scrutinee `a` rather than `n` | kills 2, but the run **did not complete** — see below |
| M11 `floorRoot` guard scrutinee `succ n` | kills 5 of 6 |

Four of those rows need saying out loud rather than tabulating.

**M8 is ADR-1230's third outcome in its definition-shaped form: admitted, every
value unchanged, and not the declaration meant.** A delta height below
`Nat.pow` and `Nat.mod` is a real unfolding-order hazard and nothing in this
file — nor `axiom_footprint`, nor the prelude build, nor the environment-derived
coverage assertion — can see it. It is reported as a gap rather than papered
over: an evaluation suite measures what a definition COMPUTES and says nothing
about how the kernel is told to unfold it.

**M9 surviving is correct, not a gap.** Fuel `succ a` is extensionally
identical to fuel `a` at every argument, including `a = 0`. A mutant that
changes no observable behaviour must survive an observational test, and a
suite that killed it would be asserting something it has no business asserting.

**M10 is reported as it behaved.** Guarding on `a` rather than `n` makes the
exponent equal to `a`, so `ceilRoot 2 12` becomes a search for `12 ∣ i ^ 12`
over unary numerals — pathological, and the test binary did not finish: 3 of 6
tests reported. The two it did kill are the right two, but the other three are
**unknown for that mutant**, not passing. M7 and M11 are the clean, complete
versions of the same question and both run all six.

**M5 was PREDICTED TO SURVIVE and did not, and the prediction had already been
written down before it was measured.** A `floorRoot` scanning to `n` agrees with
the intended definition at every positive argument the other tests use
(`floorRoot 2 12 = 2 ≤ 2`, `floorRoot 3 8 = 2 ≤ 3`), so it looked like a clean
third-outcome specimen. It is caught at `a = 0`, where the mutant scans up to
`2`, finds `0 % b² = 0` immediately and returns `2` — by a test written for an
entirely different purpose. `the_scan_bound_is_a_not_n` was added anyway,
because a test that catches it *on purpose* is what you want if the `a = 0` case
is ever changed, and the doc comment now records the correction rather than the
prediction.

## Draw 11's `natural-nth-root` review, redone

`check-holdout-adjacency.py` refuses a frozen held-out family whose recorded
review no longer matches the live environment sweep, and declaring two names
containing "root" moves that sweep. Reproduced exactly:

```text
REFUSED natural-nth-root -- recorded [('root','CReal.ivt_exact_root',11), …]
                            live     [('root','CReal.ivt_exact_root',13), …]
```

The review was **performed**, not amended. All 13 declarations matching the
stems were read by name: three `CReal.ivt_exact_root*` (bisection root-finding
over a different carrier), six `Complex.*root_of_unity*` (roots of unity),
`Nat.nthRoot`/`Nat.nthRootAux` (draw 11's own construction, necessarily
self-matching), and the two new ones. The `nth` stem adds `Nat.nth`/`Nat.nthAux`
— draw 7's selector, a different function.

**The only new question is whether `ceilRoot`/`floorRoot` settle any drawn row,
and they do not, measured rather than argued:**

- They are **different functions**. `Nat.nthRoot n a` is the greatest `m` with
  `m ^ n ≤ a` — an ORDER statement. `floorRoot`/`ceilRoot` are the adjoints of
  `b ↦ b ^ n` on the DIVISOR lattice. `floorRoot 2 12 = 2`, `ceilRoot 2 12 = 6`
  and `nthRoot 2 12 = 3`, all three asserted in the committed test suite.
- The boundary conventions differ too: `nthRoot 0 a = 1` while
  `ceilRoot 0 a = floorRoot 0 a = 0`.
- **Substituting `floorRoot` into a drawn row makes it FALSE, not merely
  unproved.** `Nat.le_nthRoot_iff` reads `a ≤ n.nthRoot b ↔ a ^ n ≤ b`, and at
  `(n, a, b) = (2, 3, 12)` the `floorRoot` form is `3 ≤ 2` (false) `↔` `9 ≤ 12`
  (true).
- `shape_search --const Nat.nthRoot` is **ABSENT** at 2708 declarations, with a
  working positive control: no declaration in this kernel mentions `Nat.nthRoot`
  anywhere in its type, so the kernel has still never proved a theorem ABOUT it.
  That is the previous review's finding, re-derived rather than inherited.
- The ten drawn rows are unchanged: the churn screen reports 0 of 42 families.

**Two things recorded because they are awkward, neither of which refuses the
family:**

1. **The stem sweep is a NAME sweep.** `ceilRoot`/`floorRoot` matched it only
   because they contain the letters "root", and had this lane named them
   `Nat.divisorFloor` the sweep would not have moved at all while the genuine
   adjacency question would have been exactly as live. The count is a trigger
   for reading; it is never evidence on its own.
2. **A SHAPE adjacency does exist and should be watched.**
   `Nat.pow_dvd_iff_dvd_floorRoot` (`a ^ n ∣ b ↔ a ∣ n.floorRoot b`) is the
   divisibility adjunction and the held-out `Nat.le_nthRoot_iff` is the order
   adjunction, so their proof SKELETONS would rhyme. Nothing of the sort exists
   today — both `--const` probes are ABSENT — and R11 asks whether a drawn row
   is settled, which it is not. But the lane that lands `factorization_root`'s
   supporting theorems from `development` should re-run this screen first: that
   is the documented shape-2 blindness, and it would arrive through a
   legitimate development proof rather than through anything a name comparison
   sees.

## Post-declaration state

**Environment 2706 -> 2708, exactly +2**, and the kind breakdown confirms it
rather than the total alone: `definition 372 -> 374`, with `axiom 30`,
`inductive 25`, `constructor 38` and `recursor 25` all unchanged.

**Kernel.** `--lib nat_prelude::factorization_root` 6 passed / 0 failed
(nonzero, confirmed). `--lib nat_prelude::` **309 passed / 0 failed**, up from
303 — the whole prelude sweep, because one bad declaration poisons the shared
build and a filtered subset cannot see it. `clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. Both names are covered by
`nat_prelude_tests`' environment-derived `definition_names` list.

**Snapshot refresh.** `gen-autogenesis-nursery-refill.py --check` regenerates
the manifest **byte-identically** under the refreshed snapshot: 420 entries,
`development=160 held-out=150 train=110`, unchanged. Checked rather than
assumed — ADR-1095's own refresh displaced two `train` rows.

| gate | before | after |
| --- | --- | --- |
| `check-autogenesis-nursery.py` | exit 0 | exit 0 |
| `check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS` | `held_out=166 settled=0 PASS` |
| `check-holdout-closed-evaluation.py` | `PASS` | `held_out=166 closed_shaped=0 violations=0 snapshot_declarations=2708 PASS` |
| `check-holdout-adjacency.py` | 16 families, 0 refused | 16 families, 0 refused, `natural-nth-root` `reviewed` |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | exit 0 | exit 0 |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `env=2706` | exit 0, `env=2708` |
| `check-shape-duplicates.py` | — | exit 0 |
| `validate-facts.py` | — | exit 0 |
| `check-autogenesis-already-proved.py` | — | exit 0 |

The screen's control discriminates in both directions: with the constructions
removed from the environment `select()` yields **0** rows for the module, and
before the review was rewritten the stale-review check FAILED naming
`natural-nth-root` with the exact live/recorded pair.

**Blind-evaluation integrity.** No fact moved partition, no fact was
registered, `nursery-v1.json` was never touched, and no
`FAMILY_MODULES`/`FAMILY_ROUTES` edit is committed — that is the draw lane's
edit.

## Decision

**Declare `Nat.floorRoot` and `Nat.ceilRoot` — construction only (ADR-0653) —
redo draw 11's `natural-nth-root` adjacency review, and author no draw.**
Index 3 is filled.

## Consequences

- **Draw 16 is authorable, and what remains is a review rather than a
  construction.** Layout RP has `natural-primitive-recursion` at index 0 and
  `natural-integer-root` at index 3, both held-out, with R1–R10 and R12
  passing. The only remaining refusal is **R11's authorable disclosure for the
  two new families** — a review that must be performed and not asserted. Five
  honest declines are on record and every one was correct; this lane adds no
  sixth, and writes no disclosure it did not perform.

- **An inherited boundary count is a claim about a tree that does not exist.**
  ADR-1220's 3-of-10 was honest, was flagged by its own author as
  definition-relative, and was still wrong about this tree by a factor of three.
  The general rule: **any figure measured against a construction you have not
  built is a hypothesis, and the building lane owes a re-measurement.** The
  cheap way to discharge it is what this lane did — turn the reading into an
  assertion at free variables, so the next reader inherits a gate rather than a
  paragraph.

- **A construction lane can red a gate that belongs to a family it never
  touches, and the re-review is part of the work.** ADR-1220 named this cost
  and it is real: reading 13 declarations and comparing them against ten
  statements is perhaps a third of an hour, and it cannot be delegated to a
  count. It is also the screen working as designed — `Nat.floorRoot` and
  `Nat.nthRoot` ARE adjacent enough to deserve a look, and the look is what
  establishes they are different propositions.

- **Two mutants survived and the report says so.** The habit worth carrying is
  not "eleven mutants, nine kills" but that M8 names a class of defect this
  suite structurally cannot reach (reducibility hints), M9 SHOULD survive, M10's
  run did not complete and its other three results are unknown rather than
  passing, and M5's predicted survival was wrong and was corrected in the source
  before it was published. A mutation table with no survivors and no corrections
  is usually a table that was not run.

- **`Nat.findGreatest` was available and unused, and that is worth knowing for
  the next lane.** It is the right shape for `floorRoot` and costs a
  `DecidablePred` witness for divisibility. Anyone landing the supporting
  theorems may want to prove `floorRoot n a = findGreatest (fun b => b ^ n ∣ a) a`
  rather than re-deriving the search's properties from scratch.
