# ADR-1975: valid-universal elimination spends 24 seconds to prevent a 107-millisecond refutation

Status: accepted
Index-summary: The three `UFDT` siblings are censused over their WHOLE winnable sets (316 rows across four divisions) and the first finding is that **the brief's own board row was stale by 69 files** — `UFDTNIRA` is **74 / 200 on the current tree, not 5**, because other lanes' datatype and dispatch work had already landed. What is left is TWO targets, not one. **`UFDTNIRA` is COST-bound**: 93 of 103 classified rows are CLOCK and **56 are one rung** — valid-universal elimination runs one quantifier-free SUB-SOLVE per top-level assertion, each handed the ladder's whole remaining clock, and 69 of the pinned 200 spend the ENTIRE budget inside it and give up PAST the deadline (median 46 ms over, **no fast declines at all**), with the rungs below never running. Across the four divisions that rung is the bounding route on **167 of 800 files and DECIDES 0 of them**. **`UFDTLIRA`, `UFDT` and `AUFDTLIRA` are SHAPE-bound by ONE predicate**: the three datatype-EXACTNESS preconditions (ADR-1920/1935/1946) are **124 of 316 rows**, every one declining with a median 23.9 s of 24 s UNSPENT — sized and handed off, with a static instrument showing **97 of the 124 are NESTED but not recursive** (field-chain depth ≤ 6) against a control in which 86 of 192 are flat. Both numbers needed a split the census would not have made: `budget exhausted after <stage>` is FOUR rungs sharing one string and `mbqi declined an unsupported fragment: …` is at least FOUR causes sharing a prefix — ADR-1956's defect, one stage up, twice. The reserve the first implies is built as a one-binary env lever, **sized by its one-way CEILING arm and then shipped at a DIFFERENT value**: ceiling `=1` gives `UFDTNIRA` **74 → 93 (+19 / −0)** but loses **2** files on the `UF` control, reproducibly; `=4` gains the **IDENTICAL 19 files** and loses **0**. **It ships ON at `share = 4`** — 0 sat↔unsat flips in 4,000 solves, all 19 re-run 3x per arm as stable GAIN with 55 comparisons against `:status`/z3/cvc5 and **0 disagreements, 0 rows nothing could check**, against a measured noise band of **0–1 files over three independent base-arm runs**. The generalisable half: a one-way ceiling answers "is anything reachable?", never "what should the constant be" — ADR-1970 shipped OFF because its ceiling was worth nothing, and a lane whose ceiling IS worth something must still run the shipped value against the control. Soundness: 901 independent comparisons on the census board, 0 disagreements; 3 mutations, 3 killed, exactly one test each.
Index-status: accepted
Date: 2026-09-13

## Context

`UFDTNIRA`, `UFDTLIRA` and `UFDT` were briefed as one target — the siblings of
`AUFDTLIRA`, which went 0 → 41 → 69 → 71 → 90 → 110 in a single day on datatype
and dispatch work ([ADR-1927], [ADR-1935], [ADR-1942], [ADR-1946],
[ADR-1966]) — with the question "how much of that transfers, and what is left
over?"

All three were censused over the **whole** winnable set of each, plus
`AUFDTLIRA` as the sibling of record, on the current tree and at the pinned
boards' own envelope. The artifacts, every runner and every derivation are in
[`bench-results/ufdt-family-20260913/`](../../../bench-results/ufdt-family-20260913/README.md).

### The first finding is that the target had already moved

| division | pinned board | measured here | winnable (was) |
|---|---:|---:|---:|
| UFDTNIRA | 5 / 200 | **74 / 200** | **109** (178) |
| UFDTLIRA | 66 / 200 | **105 / 200** | **76** (115) |
| UFDT | 22 / 200 | **31 / 200** | **51** (60) |
| AUFDTLIRA | 0 / 200 | **96 / 200** | **80** (176) |

The brief sized `UFDTNIRA` at "5 of 200, 178 winnable, the biggest
refutation-bound population on any board now that AUFLIRA and AUFNIRA have been
closed." It is 74, and the 69 files that closed were closed by other lanes'
work landing on `main` between the board being taken and this census. **The
answer to "how much transferred" is "most of it, and it is already shipped."**
This repository's own rule — *verify a blocker still exists before treating it
as one, including a blocker this file names* — is the one the brief did not
follow, and re-deriving the board row is the cheapest step in a lane.

Soundness on the re-measured rows, with the comparable denominator on the same
line ([ADR-1957]): **901 independent comparisons against `:status`, z3 4.13.3
and cvc5 1.3.4, 0 disagreements.** `summarize.py` exits non-zero on a
disagreement.

### What is left is not one target but two, and they are not the same kind

316 winnable rows censused under [ADR-1936] / [ADR-1941] / [ADR-1950] /
[ADR-1956]:

- **`UFDTNIRA` is COST-bound.** 93 of its 103 classified rows are CLOCK, and
  **56 of them are one rung**.
- **`UFDTLIRA`, `UFDT` and `AUFDTLIRA` are SHAPE-bound by one predicate.** The
  three datatype-**exactness** preconditions are **124 of 316 rows** across all
  four divisions, every one declining with a median 23.9 s of 24 s unspent.

Both numbers required a split the census would not have made on its own, and
both splits are the same defect [ADR-1956] names, one stage up:

- `quantified solve time budget exhausted after <stage>` is **four different
  rungs sharing one string**. Merged, `UFDTNIRA` reads "56 rows, the quantified
  ladder ran out of time" — a finding with no lever in it. Split, it names one
  function.
- `mbqi declined an unsupported fragment: …` is a **prefix shared by at least
  four causes**. Merged it is one 92-row bucket; split, the three named
  datatype-exactness preconditions are 85 of those 92.

This ADR is about the first. The second is sized in the README's section 5 and
handed off.

## The rung

`finish_quantified_solve` runs valid-universal elimination near the top of the
quantified ladder. It is a sat-side universal-closure validity check: a
top-level `∀x. body` with a quantifier-free body is valid iff `¬body[x := c]` is
unsat for a fresh constant `c`, and a proven-valid universal is replaced by
`true`. `eliminate_valid_universals` runs **one quantifier-free SUB-SOLVE per
top-level assertion**, each handed `config_with_remaining_timeout(config,
deadline)` — the ladder's whole remaining wall clock — and the ladder's own
deadline check sits *after* the call.

On `UFDTNIRA` that is exactly what happens. **69 of the pinned 200 (56 of the
109 winnable) spend the entire budget inside the pass and give up PAST the
24,000 ms deadline**, median 46 ms over, minimum 30 ms over, maximum 77 ms
over — a distribution with no fast declines in it at all. The seventeen-odd
rungs below never run.

This is [ADR-1970]'s shape in a different rung: one route holding the whole
quantified clock and starving the ladder. Two things differ, and both matter:

1. It is **three times larger** — 56 rows of one division's 109 winnable
   against `q:egraph`'s 23 of 54 — and it is the largest CLOCK family on any
   datatype division.
2. The polarity is unambiguous: `UFDTNIRA`'s winnable set is **109 unsat, 0
   sat**. Handing clock to the refutation rungs below is aimed at a population
   made entirely of refutations, which is the [ADR-1971] check applied *before*
   sizing rather than after.

And the [ADR-1971] decline-time check comes out the other way round here, which
is why this was worth building rather than killing: ADR-1971's target declined
in **0.11 s at a 300 s budget** — no route ran, so a rule added to a route
reached nothing. These rows consume 24,000 ms. A route IS running. The only
open question is whether a *different* route decides the file with that clock,
and that is a measurement.

## The lever

`QuantValidUniversalReservePolicy` in `crates/axeyum-solver/src/auto.rs`, the
same shape as [ADR-1970]'s `QuantEgraphReservePolicy` and selected the same way,
by `AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE`, so **both arms come out of one
binary** and an A/B can never accidentally compare two builds.

- `off` / `0` / empty / unparseable / absent → `WholeBudget`, byte-identical to
  the pre-lever code. A typo must never select an arm nobody chose.
- `on` → `LadderReserve { share: QUANT_VALID_UNIVERSAL_LADDER_RESERVE_SHARE }`
  (4, the value every other ladder reserve here settled on).
- `n >= 1` → `LadderReserve { share: n }`, which is how `share = 1` is reached.

**`share = 1` is the CEILING arm**: the pass gets `MIN_LADDER_SLICE` (1 ms) and
the ladder below gets essentially the whole clock — strictly more than any real
reserve can give. A file the ceiling arm does not decide is out of reach of
every reserve, so the sizing is ONE-WAY.

### Why bounding this pass is sound at any budget

The pass REWRITES the assertion set, which `q:egraph` does not, so it carries a
hazard [ADR-1970]'s lever did not have: proving validity is a sub-solve, and a
bounded budget can cut one off mid-flight. If the pass ever replaced a universal
with `true` on an unfinished sub-solve, it would weaken the query — producing a
wrong `sat` on a refutable one and masking a genuine `unsat`.

It cannot, and the reason is structural rather than incidental:
`eliminate_valid_universals` rewrites an assertion **only** on
`try_eliminate(...) == Ok(Some(_))`, which is returned only after the sub-solve
returns `Unsat`; its per-assertion loop tests `config_with_remaining_timeout`
BEFORE each attempt and, when the budget is spent, copies **every remaining
assertion through unchanged** (`out.extend_from_slice(&assertions[index..])`).
A smaller budget therefore eliminates **fewer** universals and never a different
set. That is the whole soundness argument, and the suite below is written to
fail if it ever stops being true.

## The measurement

One binary, three environments, the **full pinned 200** of five divisions (not
the winnable subset, so a loss outside it is visible), 24 s / 8 GiB / one pinned
physical core, arms back to back on the same file with the order alternating.
Protocol and derivations: [`AB.md`](../../../bench-results/ufdt-family-20260913/AB.md).

| arm | UFDTNIRA | UFDTLIRA | UFDT | AUFDTLIRA | UF (control) |
|---|---:|---:|---:|---:|---:|
| ceiling `=1` | **74 → 93 (+19 / −0)** | 105 → 105 | 31 → 31 | 96 → 96 | 90 → 88 (**−2**) |
| **shipped `=4`** | **73 → 92 (+19 / −0)** | 105 → 105 | 31 → 31 | 96 → 96 | 90 → **90 (0 / 0)** |

**0 sat↔unsat flips in 4,000 solves.**

### The noise floor, before the effect

ADR-1970 declined to ship on exactly this check — its base arm read 73 in the
A/B and 76 in the census sweep at the same commit, a 3-file band around a +2
effect. Here three independent runs of the base arm over 800 files (the census
sweep and both A/Bs' base arms) **disagree on exactly one file**, and it is
named: `R509-011__higher_order_proof__why_cff6fc_…` decides `unsat` in 2,714 ms
on the quiet run and times out at 24,132 ms on the run that overlapped twelve
other shards — an ambient-load flip on a file that decides near the budget.
**A band of 0–1 against a +19 effect.**

### Every moved row re-checked, three times per arm

    rows re-checked: 21   GAIN 19   LOSS 2   UNSTABLE 0   CONTRADICTED 0
    NO INDEPENDENT CHECK AT ANY BUDGET (ADR-1957): 0 of 21

    the 19 gains:  vs :status 18/18   vs z3 18/18   vs cvc5 19/19   DISAGREEMENTS 0

55 independent comparisons behind the 19 and **0 rows with no opportunity for a
disagreement**, so the zero is not vacuous ([ADR-1957]). Every one reads
`base=[unknown,unknown,unknown] arm=[unsat,unsat,unsat]`: not one is the
~1–1.5 % of files that flip on ambient load at a 24 s budget. All 19 are
`unsat`, which is what a division that is 0 % satisfiable can produce.

### Why `share = 4` and not the ceiling

**The two arms gain the IDENTICAL set of 19 files** — compared as a set, not as
a count — so the gain is not an artefact of an extreme setting. What separates
them is the control: the ceiling arm loses **2** `UF` files and `share = 4`
loses **0**. Both losses are as stable as the gains
(`base=[unsat,unsat,unsat] arm=[unknown,unknown,unknown]`, with independent
agreement that `unsat` is right) and they are reported as a real cost rather
than explained away.

**A one-way ceiling answers "is anything reachable?" It does not answer "what
should the constant be."** The ceiling arm was the right sizing instrument and
the wrong thing to ship, and only the control could tell the two apart. This is
the generalisable half of this ADR: [ADR-1970] ran the ceiling and shipped OFF
because the ceiling was worth nothing; a lane that finds its ceiling worth
something must still run a real value against the control before shipping it,
because the ceiling's cost is not the shipped value's cost.

### The shape of the gain

Under the ceiling arm 16 of the 19 decide in **106–109 ms**. Under `share = 4`
the same 19 land at **18,116–19,023 ms** — the pass spends its 18 s slice first
and the ladder's 6 s reserve then refutes in about a tenth of a second. Every
one is a file on which the base arm spends the full 24,000 ms inside
valid-universal elimination and then declines.

**The pass was spending twenty-four seconds to prevent a hundred-millisecond
refutation.**

## Decision

**Ship the reserve ON at `share = 4`.** The default policy becomes
`LadderReserve { share: QUANT_VALID_UNIVERSAL_LADDER_RESERVE_SHARE }`;
`AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE=off` selects the historical `WholeBudget`
so the A/B against the pre-ADR code stays runnable, and `=1` keeps the ceiling
arm runnable for a future re-sizing.

The parse contract inverts with the default, deliberately: an absent, empty,
`on` or **unparseable** value resolves to the SHIPPED reserve. The rule is
**"unknown input means what we ship"**, not "unknown input means no reserve" —
they coincided while the lever shipped off and stopped coinciding the moment
the measurement came in. A typo must never select an arm nobody chose, and
after this ADR the arm nobody chose is `WholeBudget`.

This follows the pattern `UF_ARITH_CEGAR_SLICE` already ships: an unconditional
`all_but_reserve(..., 4)` on a ladder rung, with the share measured rather than
inherited.

**What this does NOT decide.** The rung is the bounding route on 167 of 800
files across the four datatype divisions and decides **0** of them, but that is
a statement about these divisions. The rung exists because some other fragment
needs it, nothing here measures that, and this is why the change is a RESERVE
and not a removal.

## The guards

`crates/axeyum-solver/tests/quant_valid_universal_reserve_row.rs`, registered in
`hooks/pre-push`. Every fixture runs under **all three arms** (`WholeBudget`,
reserve 1/4, and the `share = 1` ceiling), and each adversarial **satisfiable**
query is pinned `Sat` — not merely "not `unsat`" — because an `unknown` would
skip the in-test model replay and leave the adversarial half checking nothing.
Each has an `unsat` twin in the same file differing in ONE small term, so the
pair cannot be passed by a solver that answers `sat`/`unknown` to everything.

The fixture that carries the hazard specific to THIS pass is
`a_nonvalid_universal_refuted_at_one_ground_term_is_unsat_under_any_arm`:
`∀x. f(x) ≥ 0` with `f(0) = −5`. Delete that universal — which is what a pass
eliminating on an unfinished sub-solve would effectively do — and the residual
is satisfiable, so the wrong behaviour turns this row's `unsat` into `sat`. It
is the only fixture here that can see it.

Three unit tests sit beside the code in `auto.rs`: the parse table (everything
unrecognised is the shipped default), the per-arm budget arithmetic (the default
arm must hand the pass the budget UNCHANGED — the mutant that makes the reserve
unconditional dies here), and an unbounded caller budget staying unbounded.

[ADR-1927]: adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md
[ADR-1935]: adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md
[ADR-1936]: adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md
[ADR-1941]: adr-1941-attempts-alone-cannot-classify-a-census-row-the-open-segment-is-the-discriminator.md
[ADR-1942]: adr-1942-a-constructor-term-as-a-uf-argument.md
[ADR-1946]: adr-1946-a-datatype-valued-uf-result-the-witness-is-a-variable-and-the-scan-has-not-run-yet.md
[ADR-1950]: adr-1950-a-round-budget-and-a-clock-budget-are-different-findings-and-a-census-must-not-merge-them.md
[ADR-1956]: adr-1956-do-not-raise-the-instantiation-round-ceiling-zero-of-the-177-rows-reach-it.md
[ADR-1957]: adr-1957-a-zero-disagreement-claim-must-publish-its-comparable-denominator.md
[ADR-1966]: adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[ADR-1970]: adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md
[ADR-1971]: adr-1971-outer-read-over-write-is-worth-zero-alia-and-abv-are-held-by-satisfiability.md
