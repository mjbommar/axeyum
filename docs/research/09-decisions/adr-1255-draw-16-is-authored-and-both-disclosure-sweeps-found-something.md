# ADR-1255: Draw 16 is authored — and both disclosure sweeps found something, one of them inside the blind population

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1240 and ADR-1245 filled cycle indices 0 and 3 with
construction-only unblocks and each deliberately left R11's authorable
disclosure to the draw lane, which is the only remaining refusal. This lane
performs both reviews and authors the draw: `nursery-v2-extension.json` goes
420 -> **460** entries, held-out 150 -> **170** (`check-holdout-adjacency.py`
16 -> **18** families, `check-autogenesis-holdout-isolation.py` `held_out` 166
-> **186**, `settled=0` throughout and no row moved partition). Everything was
re-measured against a `shape_search --release` rebuilt in this worktree at
**2711** declarations — three more than ADR-1245's 2708 — with the real
`select()`/`assign_partitions()`/`screen_family()`/`guard()`, never
`propose-nursery-refill.py`. **ADR-1220's layout RP does not exist as four
single-module families and this lane had to rebuild the two fillers**: at 2711
only THREE unassigned modules carry a pool of 10 alone, and both named fillers
are short (`Mathlib.Data.Int.Fib.Basic` yields 6, `Mathlib.Data.Int.NatPrime`
yields 2), so `select()` RAISES on the literal reading. Index 0's pool is still
**11 against a floor of 10** and both drawn tens reproduce ADR-1240's and
ADR-1245's verbatim. **The two disclosures each found a gap in the SCREEN and
one found something inside the blind population**: the stem sweep misses
`Nat.casesOn` and `Nat.floorRoot` (both below the 3-row characteristic floor
while a drawn row is about them — hand-swept, both empty); `Nat.Primrec.of_eq`
looks unreachable without `funext`, which this kernel deliberately lacks; and
**`Nat.ceilRoot_pow_self` and the standing held-out `Nat.nthRoot_pow` are the
same statement with a different root function**, so the blind population's two
"root" families are not independent signals. That is not a leak and R11 is
right to be clean, and it is disclosed because an undisclosed correlation
inside a blind population overstates its breadth the way a leak does. The four
advisory-undisclosed standing families are measured and **declined**, with
reasons. Five gates green.

Related: ADR-1240 (index 0), ADR-1245 (index 3, and the two findings carried
forward), ADR-1220 (layout RP and the two screens), ADR-1175 (draw 15, and the
dispatch-supply way of choosing a filler), ADR-1160 (the boundary-equation
READING), ADR-0768 (R11 and its disclosure review), ADR-0695/ADR-0950 (R12),
ADR-0653 (the adjacency rule and construction-only unblocks), ADR-0542 (the
amendment ledger)

## What was verified before anything was written

`shape_search --release` was rebuilt in this worktree rather than trusted from
a prebuilt binary — the documented stale-index hazard, where a false ABSENT is
the expensive verdict and a stale binary also misreports what is PRESENT.

**Session start: 2711 declarations against the committed snapshot's 2708.**
Three had landed since ADR-1245: `Int.firstSupplementaryLawResidue`,
`Int.wilsonHalfSplit`, `Nat.sub_sub_self`. None touches either candidate
family. The snapshot was refreshed with `--snapshot-from`, and
`gen-autogenesis-nursery-refill.py --check` then regenerates the pre-draw
manifest **byte-identically** — checked rather than assumed, because ADR-1095's
own refresh displaced two `train` rows.

Baseline, all five gates green before any edit:

| gate | before |
| --- | --- |
| `check-autogenesis-nursery.py` | exit 0 |
| `check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS` |
| `check-holdout-closed-evaluation.py` | `held_out=166 closed_shaped=0 violations=0 snapshot_declarations=2708 PASS` |
| `check-holdout-adjacency.py` | 16 families, 0 refused, 4 undisclosed |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | exit 0 |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `env=2708` then `env=2711` |

The screen is `docs/research/09-decisions/adr-1255-draw-16-screen.py`, built the
same way as ADR-1240's and ADR-1245's: it loads
`gen-autogenesis-nursery-refill.py`, `check-holdout-adjacency.py` and
`check-holdout-closed-evaluation.py` by path and calls the ACTUAL functions,
injecting the four candidate families into `FAMILY_MODULES`/`FAMILY_ROUTES` in
memory so it can be run before the generator is edited and re-run afterwards.
`propose-nursery-refill.py` is deliberately not a candidate space (ADR-1160: it
mirrors only the hygiene screen and OVERCOUNTS — it once gave 21 where the real
screen gave 6).

## The first correction: layout RP does not exist as four single-module families

ADR-1220's table reads

```text
LAYOUT RP -- both slots solved
  [0] natural-primitive-recursion     held-out
  [1] natural-fibonacci               development
  [2] natural-prime-divisibility      train
  [3] natural-integer-root            held-out
```

and the two later ADRs simulated it with single modules. Run through the real
`select()` at env 2711, that raises:

```text
RefillError: family 'natural-fibonacci-basic' yields 6 screened candidates,
             fewer than the 10 the refill takes
```

Measured exhaustively over every unassigned module: **exactly three carry a
screened pool of 10 or more on their own** —
`Mathlib.Computability.Primrec.Basic` (11),
`Mathlib.Data.Nat.Factorization.Root` (18) and
`Mathlib.NumberTheory.FactorisationProperties` (15, refused for held-out by
ADR-1115 and recorded in the review file's `refused` list). Two of those three
are precisely the held-out candidates. `Mathlib.Data.Int.Fib.Basic` yields 6
and `Mathlib.Data.Int.NatPrime` yields 2.

ADR-1220's own table said so — "fibonacci (**2 modules**)", "prime divisibility
(**7 modules**)" — and the two intervening ADRs dropped the parenthetical when
they simulated the layout. The bundles are rebuilt here at today's environment
rather than inherited:

```text
natural-fibonacci-basic     Mathlib.Data.Int.Fib.Basic   6
                          + Mathlib.Data.Nat.Fib.Basic   8   = 14
natural-prime-divisibility  Mathlib.Data.Int.NatPrime    2
                          + Mathlib.Data.Nat.GCD.Prime   3
                          + Mathlib.Data.Nat.Prime.Factorial 3
                          + Mathlib.Data.Nat.Prime.Int   2
                          + Mathlib.RingTheory.Int.Basic 3   = 13
```

**Index 1's primary module is effectively forced**, which is worth stating
because it removes any suspicion the filler was chosen for an outcome: the sort
window between `Mathlib.Computability.Primrec.Basic` and
`Mathlib.Data.Int.NatPrime` contains exactly one unassigned module with a pool
above 1, and it is `Mathlib.Data.Int.Fib.Basic`.

**`Mathlib.Data.Nat.Prime.Nth` (5 further rows) was available and is
deliberately NOT taken.** It is the nth-prime module and `natural-nth-selector`
is a STANDING held-out family whose subject is `Nat.nth`. **R11 would not have
seen it**: `cmd_check` scores a held-out family only against families drawn no
later than itself, so a draw-16 train family cannot make a draw-7 held-out
family go red however adjacent it is. That asymmetry is deliberate — a later
draw must not retroactively refuse the standing population — and it is not a
licence to publish a subject an existing held-out family owns. The bundle
reaches 13 without it.

The screen therefore also runs a check **no gate performs**: every standing
held-out family re-scored with this draw's development/train families added to
the published set and the draw-membership filter removed. All 16 are unmoved,
topic and vocabulary both, and the run prints the before/after pair per family
rather than a summary.

## The layout, through the real machinery

```text
environment: 2711 declarations (live dump)
ok    construction Nat.Primrec is in the environment
ok    construction Nat.casesOn is in the environment
ok    construction Nat.floorRoot is in the environment
ok    construction Nat.ceilRoot is in the environment

cycle assignment over the four fresh families, in sort order:
  [0] natural-primitive-recursion   held-out     Mathlib.Computability.Primrec.Basic
  [1] natural-fibonacci-basic       development  Mathlib.Data.Int.Fib.Basic
  [2] natural-prime-divisibility    train        Mathlib.Data.Int.NatPrime
  [3] natural-integer-root          held-out     Mathlib.Data.Nat.Factorization.Root

ok    cycle reproduces layout RP
ok    the draw adds 40 entries
ok    control: natural-primitive-recursion yields 0 without its constructions
ok    control: natural-integer-root yields 0 without its constructions
ok    R12: no new held-out row is a closed evaluation  []
R11 natural-integer-root         clean  topic=0 vocab=0/10 env=['root','ceil','ceilroot']
R11 natural-primitive-recursion  clean  topic=0 vocab=0/10 env=['pair','primrec','unpaired']
ok    no existing family's drawn ten churns  []
ok    no standing held-out family's recorded review goes stale  []
ok    no standing held-out family's signals move under this draw's
      development/train families  []

ADR_1255_DRAW_16_SCREEN|env=2711|new_entries=40|churn=0|stale_reviews=0
                       |r12_violations=0|failures=0
```

`Mathlib.Computability.*` sorts before every `Mathlib.Data.*`, so index 0 falls
out of the alphabet rather than out of an arrangement. Both controls
discriminate: with the constructions removed from the environment `select()`
refuses each family by name with `yields 0 screened candidates`.

**Index 0's pool is 11 against `PER_FAMILY = 10`, re-measured rather than
inherited.** One row of slack, the tightest margin any draw has had. If two of
those eleven ever become catalogued or unstatable, `select()` raises and the
whole refill fails.

**Both drawn tens reproduce their ADRs verbatim**, printed by the screen and
read rather than counted (ADR-1160's rule: `is_closed_evaluation` is
binder-free by construction, so a quantified defining equation is invisible to
it). `natural-primitive-recursion` is ten closure properties with no defining
equation in any form; `natural-integer-root` is ADR-1245's list unchanged, with
`Nat.ceilRoot_zero_left` the single boundary row it discloses.

## Disclosure sweep 1 — `natural-primitive-recursion`

Live sweep, recorded verbatim in the review file:

```text
[["pair", "CPoint.cevian_pair_meet", 20],
 ["primrec", "Nat.Primrec", 9],
 ["unpaired", "Nat.unpaired", 1]]
subjects: Nat.Primrec, Nat.pair, Nat.unpaired
```

Every declaration those stems reach was enumerated and read.

- **`primrec` (9) is exactly ADR-1240's construction and nothing else**: the
  inductive `Nat.Primrec`, its seven constructors (`zero`, `succ`, `left`,
  `right`, `pair`, `comp`, `prec`) and the recursor `Nat.Primrec.rec` —
  necessarily self-matching, and disjoint from the drawn ten (`add`,
  `casesOn'`, `casesOn1`, `const`, `mul`, `of_eq`, `pow`, `prec1`, `pred`,
  `swap`) by name and by statement. The near miss is real and is not one:
  `Nat.Primrec.prec` is the general two-premise constructor and drawn
  `Nat.Primrec.prec1` is its specialization at a constant `m`, a different
  proposition needing a derivation.
- **`pair` (20) is dominated by word collisions across four carriers.**
  `Nat.Pair` and its eight projections and extensionality lemmas are the PAIR
  INDUCTIVE from the `binaryRec` lane — a structure type, not Cantor pairing.
  `Nat.restrict_pair_injective`, `Nat.restrict_pair_maps_into` and
  `Int.prod_range_pairing_collapse` are the Wilson/totient
  transposition-pairing lemmas, stated over `injectiveOn`/`mapsInto` and
  mentioning `Nat.pair` nowhere — verified by their RENDERED TYPES, not by
  their names. `CPoint.cevian_pair_meet`, `CReal.geom_pair_within` and
  `Rat.PairwiseUncorrelated` share only the word.
- **Mechanical, each against a working positive control**
  (`shape_search --const Nat.countRange` → FOUND 21): `--const Nat.Primrec` →
  FOUND 8 (seven constructors and the recursor); `--const Nat.pair` → FOUND 3;
  `--const Nat.unpaired` → FOUND 2. **No theorem in this kernel mentions
  `Nat.Primrec`, `Nat.pair` or `Nat.unpaired` in its type at all.**

### Finding 1 — the sweep does not reach `Nat.casesOn`

`subject_constants` keeps a constant characteristic of at least
`max(2, 0.30 × 10) = 3` rows. `Nat.casesOn` occurs in exactly two drawn rows
(`casesOn'`, `casesOn1`), so it is not a subject and the stem `caseson` is
never swept — **even though two drawn rows are about it**. This is a gap in the
SCREEN, not in the family. Hand-swept: exactly one declaration, `Nat.casesOn`
itself, ADR-1240's definition, with nothing stated about it.

### Finding 2 — `Nat.Primrec.of_eq` looks unreachable, and that is disclosed

`Primrec f → (∀ n, f n = g n) → Primrec g` transports a `Prop` indexed by a
FUNCTION along a POINTWISE equality, which Mathlib discharges with `funext`.
**This kernel is intuitionistic and deliberately has no `funext`, no `propext`
and no `Classical.choice`** (`crates/axeyum-lean-kernel/src/prelude.rs:61`,
with a dozen sites working around the absence); the environment sweep for the
stems `funext`, `propext` and `choice` returns 0, 0 and 0. The recursor gives
no route either: a motive `fun f _ => ∀ g, (∀ n, f n = g n) → Primrec g` leaves
the `zero` case needing `Primrec g` for an arbitrary pointwise-zero `g`, which
no constructor supplies.

**This is a review's reading and not an established impossibility** — no proof
was attempted, and this repository's own record on "cannot be done here" is
poor (ADR-0840 corrected three sizings of one target). It is recorded because
one of the ten rows may be blind in the strong sense of *unestablishable*
rather than merely unproved, which is the opposite of contamination and still
overstates the population's usable breadth if nobody says so.

## Disclosure sweep 2 — `natural-integer-root`

```text
[["root", "CReal.ivt_exact_root", 13],
 ["ceil", "Nat.ceilRoot", 2],
 ["ceilroot", "Nat.ceilRoot", 1]]
subjects: Nat.ceilRoot
```

- **`root` (13)**: three `CReal.ivt_exact_root{,_at,_decides_sign}` (bisection
  root-finding for the intermediate value theorem — a different carrier and a
  different question), six `Complex.*root_of_unity*`/`IsRootOfUnity`/
  `I_is_fourth_root` (roots of unity), `Nat.nthRoot`/`Nat.nthRootAux` (draw
  11's ORDER root) and `Nat.ceilRoot`/`Nat.floorRoot` (this family's own
  construction). **`ceil` (2)**: `Nat.ceilRoot` and `Nat.half_ceil_parity`, the
  latter about the parity of `(n+1)/2`. **`ceilroot` (1)**: the definition.
- **Mechanical**: `--const Nat.ceilRoot`, `--const Nat.floorRoot` and
  `--const Nat.nthRoot` are all ABSENT at `declarations=2711` from a binary
  built in this worktree, against `--const Nat.countRange` FOUND 21.

### Finding 3 — the sweep does not reach `Nat.floorRoot` either

Same threshold gap: `Nat.floorRoot` occurs in exactly ONE drawn row
(`Nat.floorRoot_eq_zero`), below the 3-row floor, so it is not a subject and
the stems `floor` and `floorroot` are never swept although a drawn row is about
it. Hand-swept: `floorroot` → 1 (the definition); `floor` → 3 (the definition
plus `CReal.bucketIndexFloorLower` and `CReal.bucketIndexFloorUpper`, the
unit-fraction grid clamps in `creal/uniform_continuity.rs`). Empty — **but a
review that ran only the automated sweep would not have known that**, and two
independent instances of the same threshold gap in one draw is a pattern rather
than an accident.

### ADR-1245's two carried findings, re-derived

- **The stem sweep is a NAME sweep.** Had ADR-1245 named these
  `Nat.divisorFloor`/`Nat.divisorCeil` the `root` sweep would not have moved at
  all while the adjacency question was exactly as live; had ADR-1240 named the
  predicate `Nat.Rec` the `primrec` sweep would have been swamped. The count is
  a trigger for reading and is never evidence on its own.
- **`floorRoot`/`ceilRoot` are DIVISIBILITY roots; `Nat.nthRoot` is an ORDER
  root.** `floorRoot 2 12 = 2`, `ceilRoot 2 12 = 6`, `nthRoot 2 12 = 3`, all
  three kernel-checked in `nat_prelude/factorization_root_tests.rs` rather than
  hand-computed here. Substituting `floorRoot` into the held-out
  `Nat.le_nthRoot_iff` (`a ≤ n.nthRoot b ↔ a ^ n ≤ b`) at `(n, a, b) =
  (2, 3, 12)` gives `3 ≤ 2` (false) `↔` `9 ≤ 12` (true), so the two families'
  rows are not the same propositions.

### Finding 4 — the rhyme is already live between two BLIND rows

ADR-1245 framed the shape-2 risk prospectively: *"whoever lands
`factorization_root`'s supporting theorems from `development` should re-run
this screen first."* That is right and still stands. But the rhyme exists
today, between rows nobody has published, and nothing in this draw creates it:

| drawn (draw 16, held-out) | standing (draw 11, held-out) |
| --- | --- |
| `ceilRoot_pow_self : n ≠ 0 → ∀ a, n.ceilRoot (a^n) = a` | `nthRoot_pow : n ≠ 0 → ∀ a, n.nthRoot (a^n) = a` |
| `ceilRoot_one_right : n ≠ 0 → n.ceilRoot 1 = 1` | `nthRoot_one_right : n.nthRoot 1 = 1` |
| `ceilRoot_zero_left : ceilRoot 0 a = 0` | `nthRoot_zero_left : nthRoot 0 a = 1` |
| `dvd_pow_iff_ceilRoot_dvd` (divisibility adjunction) | `le_nthRoot_iff` (order adjunction) |

The first pair is the **same statement** with a different root function.

**This is not a leak and R11 is right to be clean.** ADR-0653's rule is about a
held-out family whose mathematics a DEVELOPMENT or TRAIN family already
publishes; `natural-nth-root` is held-out, nothing about `Nat.nthRoot` is
published, and `--const Nat.nthRoot` is ABSENT. What it does mean is that the
blind population's two "root" families are **not independent signals**: a route
that establishes `ceilRoot_pow_self` very probably establishes `nthRoot_pow` by
the same skeleton, so whoever reads a held-out result over either should count
the two as roughly one capability rather than two. It is disclosed because an
undisclosed correlation inside a blind population overstates its breadth in
exactly the way a leak does, by a different mechanism — and because no screen
we have asks the question: R11 compares held-out against published, never
held-out against held-out.

## The four advisory-undisclosed standing families: measured, and declined

`check-holdout-adjacency.py` reports four held-out families with a non-empty
environment sweep and no recorded review. They are advisory here and are
**REFUSED at draw time only for families a draw ADDS**, so none of them blocks
this draw. Each was swept anyway, because "it does not block me" is not an
answer to whether the population is sound:

| family | draw | subjects | sweep |
| --- | --- | --- | --- |
| `natural-square-root` | 0 | `Nat.sqrt` | `sqrt` 21 |
| `integer-division-boundary-cases` | 3 | `Int.natAbs` | `abs` 73, `natabs` 4 |
| `integer-absolute-value` | 4 | `Int.natAbs` | `abs` 73, `natabs` 4 |
| `natural-nth-selector` | 7 | `Nat.nth` | `nth` 4 |

Two of the four were read in full and are clean:

- **`natural-nth-selector`** is the cheapest and the clearest. The stem `nth`
  reaches **four** declarations in the whole environment: `Nat.nth`/`Nat.nthAux`
  (draw 7's own construction, necessarily self-matching) and
  `Nat.nthRoot`/`Nat.nthRootAux` (draw 11's, an unrelated function that merely
  contains the letters). Nothing else.
- **`natural-square-root`** has the largest sweep and reads clean. Sixteen of
  the 21 `sqrt` hits are `CReal.*` — the square root over the constructed
  reals, a different carrier. The five `Nat` hits are `Nat.sqrt`, `Nat.sqrtAux`,
  `Nat.sqrt_one`, `Nat.sqrt_zero` and `Nat.no_rational_sqrt_two`; **none of the
  family's sixteen rows is `sqrt_zero` or `sqrt_one`** (they are `le_sqrt`,
  `sqrt_eq`, `sqrt_le`, `sqrt_lt`, `sqrt_pos`, `exists_mul_self`, …), and
  irrationality of √2 is a different proposition. There is a structural
  protection besides: `Nat.sqrt ∈ HELD_OUT_CONSTRUCTIONS`, so `select()`
  excludes every row mentioning it from any future pool.

**No review row is written for any of the four, and that is a decision rather
than an omission.** A `reviews` row is not merely a record — it is a live
tripwire. `screen_family` refuses a family whose recorded sweep no longer
matches the live one, *wherever it is found*, so writing a row for
`integer-absolute-value` makes every future declaration matching `abs` (73
today, in active `CReal` development) or `natabs` red the standing gate, and
the same for `sqrt` (21, likewise active). The checker's own comment already
weighs this trade for retroactive demands; the same arithmetic applies to
retroactive supply. Closing them is a separate task with a real maintenance
cost and it belongs to a lane that intends to carry it, not to a draw lane
passing through. The measurements above are recorded so that lane starts from
data rather than from the sweep counts.

## Dispatch supply, and one row that is already proved

| family | partition | closed-eval rows | already in the environment |
| --- | --- | --- | --- |
| `natural-primitive-recursion` | held-out | 0 of 10 | 0 |
| `natural-fibonacci-basic` | development | **6 of 10** | **1** (`Nat.fib_add`) |
| `natural-prime-divisibility` | train | 0 of 10 | 0 |
| `natural-integer-root` | held-out | 0 of 10 | 0 |

`natural-fibonacci-basic` is weak supply and it is stated rather than glossed:
six rows are boundary values (`Int.fib_{neg_one,one,two,zero}`,
`Nat.fib_{one,two}`) and `Nat.fib_add` is already declared here, so the family
buys roughly three rows of real work. ADR-1175 measured the same property of
the Fib/bitwise family and reached the same conclusion. It sits in
DEVELOPMENT, where a cheap row is a fast-closure feature rather than the
ADR-0542 leak (ADR-0653), and — as measured above — index 1's primary module is
effectively forced, so this is a cost of the layout rather than a choice within
it. `natural-prime-divisibility` in TRAIN buys ten rows of real work.

`check-autogenesis-already-proved.py` flags `Nat.fib_add` as `[MATCH]` and
exits 0; it is a development row, so R9 (which screens held-out only) neither
fires nor should.

## Post-draw state

**Manifest.** 420 → **460** entries. `development` 160 → 170, `train` 110 →
120, `held-out` 150 → **170**. `combined` 634 → 674. Forty fact files written
by the generator, all `open`, none settled.

| gate | before | after |
| --- | --- | --- |
| `check-autogenesis-nursery.py` | exit 0 | exit 0, `v1=216 v2=460 components=365` |
| `check-autogenesis-holdout-isolation.py` | `held_out=166 settled=0 PASS` | `held_out=186 settled=0 references=0 PASS` |
| `check-holdout-closed-evaluation.py` | `held_out=166 … PASS` | `held_out=186 closed_shaped=0 violations=0 snapshot_declarations=2711 PASS` |
| `check-holdout-adjacency.py` | 16 families, 0 refused, 4 undisclosed, 4 reviews | **18** families, 0 refused, 4 undisclosed, **6** reviews |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | exit 0 | exit 0, literal **unmoved** |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `env=2708` | exit 0, `env=2711`, reproduces |
| `check-holdout-adjacency.py --self-test` | — | 11 passed, 0 failed |
| `check-shape-duplicates.py` | — | exit 0, 15 groups, all allowlisted |
| `validate-facts.py` | — | exit 0 |
| `check-settled-fact-statements.py` | — | `settled=2253 pinned=2253 drifted=0 PASS` |

The dispatch baseline's tripwire literal did **not** move (`candidates=198
dispatchable=0 declined=22 established=176`, digest unchanged), so its audit
comment needs no amendment.

**Blind-evaluation integrity.** No fact moved partition, none was registered
as settled, `nursery-v1.json` was never touched, `settled=0` before and after,
and the held-out rise from 166 to 186 is exactly the two new families' twenty
rows.

## Decision

**Author draw 16 at layout RP**, with `natural-fibonacci-basic` and
`natural-prime-divisibility` rebuilt as multi-module bundles because the
single-module reading does not screen, and with both R11 disclosure reviews
PERFORMED and recorded in
`artifacts/autogenesis/holdout-adjacency-review-v1.json`.

## Consequences

- **The stem sweep's characteristic threshold has a systematic blind spot at
  the edge of a drawn ten**, and this draw hit it twice. A constant appearing
  in one or two of ten rows is not a subject, so its stem is never swept — and
  a family whose tenth row is about a second function (`floorRoot` beside
  `ceilRoot`, `casesOn` beside `Primrec`) is exactly the shape that produces
  it. Both were empty here. **Any future disclosure review should enumerate the
  constants of the drawn ten and hand-sweep every one the automated `subjects`
  set drops** — it is one extra command and neither reviewer would have run it
  from the sweep output alone. A screen change is not proposed: lowering the
  threshold widens every sweep and the review file's own history says the
  binding cost is reading, not sweeping.

- **R11 compares held-out against published and never held-out against
  held-out, so a correlated blind population is invisible to it.**
  `ceilRoot_pow_self` and `nthRoot_pow` are the same statement over two root
  functions and both are blind. Nothing is unlawful and nothing needs undoing;
  what is needed is that a referee reading a held-out result over either family
  knows it is close to one capability rather than two. If a third "root" family
  is ever proposed, this is the question to ask first.

- **An inherited layout is a claim about a tree that does not exist**, which is
  ADR-1245's own lesson arriving one level up. ADR-1220's layout RP was honest
  and its table said "2 modules"/"7 modules"; two later ADRs simulated it with
  single modules and neither ran `select()` over the whole four-family layout,
  because each was filling one slot. **The lane that authors a draw owes the
  first end-to-end run**, and it found the discrepancy in its first invocation.

- **A row may be unreachable rather than unproved, and the ledger has no way to
  say so.** `Nat.Primrec.of_eq` needs `funext`, which this kernel will not
  have. Such a row sits in the held-out population forever, contributing
  nothing and quietly inflating the count. This is not proposed as a gate — the
  judgement is exactly the kind a classifier gets wrong, and declaring a target
  impossible is this repository's most-corrected mistake — but a disclosure
  review is the right place to say it, and this one does.

- **The four advisory-undisclosed families are now measured, and closing them
  is a costed task rather than a vague debt.** `natural-nth-selector` is four
  declarations and would take minutes; `natural-square-root` and the two
  `natAbs` families put a permanent tripwire on high-traffic stems. Whoever
  takes it should take the cheap one first and decide the other three on the
  maintenance cost, not on the sweep count.
