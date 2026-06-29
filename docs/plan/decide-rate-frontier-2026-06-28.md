# Decide-rate frontier — where the Z3/cvc5 parity gap actually is (2026-06-28)

The [north star](00-north-star.md) makes **completeness / decide-rate** and
**measured performance** the two criteria that actually decide Z3/cvc5 parity,
and the [reality check](../../PLAN.md#where-we-are-vs-the-north-star--measured-reality-check-2026-06-28)
puts the current number at **663 / 992 decided (~67%)**, **19/35 rows
decide-strong (≥80%)**, `DISAGREE = 0` everywhere. This note decomposes the
remaining ~329 undecided instances from the committed
[SCOREBOARD](../../bench-results/SCOREBOARD.md) into a *prioritized, grounded*
frontier, so decide-rate work attacks the biggest, most tractable gaps first
rather than the loudest.

## The gap, ranked by absolute undecided count (impact)

| Rank | Division(s) | Files | Decide% | Undecided | Dominant cause | Gap class |
|---|---|---:|---:|---:|---|---|
| 1 | **QF_S** (strings) | 134 | 44% | ~75 | `Unsupported` (62) | **coverage** (string ops) |
| 2 | **QF_UF** bounded | 82 | 54% | ~38 | `Unsupported` (24) + `Unknown` (13) | coverage + depth |
| 3 | **QF_SLIA** | 50 | 30% | ~35 | `Unsupported` (29) | **coverage** (string+int) |
| 4 | **QF_NRA** cvc5 | 38 | 24% | ~29 | `Unknown` (27) | **depth** (CAD) |
| 5 | **QF_NIA** cvc5 | 39 | 54% | ~18 | `Unknown` (10) + `Unsupported` (8) | depth + coverage |
| 6 | **BV** quantified | 54 | 69% | ~17 | `Unsupported` (11) + `Unknown` (6) | quantified BV |
| 7 | quantified **LIA / UF** | 17 | 0% | ~17 | `Unsupported`/`Unknown` | quantifier coverage |
| — | QF_SEQ, QF_AUFBV(cvc5), QF_AUFLIA, QF_FF, QF_UFLIA tails | — | 56–80% | ~30 | mixed | near-strong tails |

## The strategic read (what this says)

1. **Strings are the single largest decide-rate lever.** QF_S + QF_SLIA + QF_SEQ
   ≈ **117 undecided**, overwhelmingly **`Unsupported`** — i.e. *missing string
   operator coverage*, not failed search. This is **Track-2 breadth** work
   (extend the string theory's operator/decision coverage), which is far more
   tractable and higher-ROI than the nonlinear depth gap. **Highest priority.**
2. **QF_UF (~38)** splits coverage (uninterpreted-sort handling — note the
   `overbound-uninterp-sorts` rows at 0–67%) and budget (`Unknown`). The IR
   keystone for first-class uninterpreted sorts (flagged in the gap analysis as
   *itself dominance-eligible*) is the unlock here.
3. **QF_NRA (~29) is the genuine 15-year catch-up** — `Unknown`-dominated = CAD
   depth (`nra_degree` frontier = 2). High effort, low near-term ROI; *do not*
   spend the decide-rate budget here first. Match Z3's *practical* rate, accept
   honest `unknown`.
4. **Quantifiers (BV/LIA/UF quantified ≈ 34 undecided, several rows at 0%)** are a
   coherent cluster — the e-matching/MBQI + quantified-BV path needs depth. Tied
   to the **e-graph + CDCL(T) keystone** (Track 1, P1.4/P1.5).
5. **`Unsupported` vs `Unknown` is the triage axis.** `Unsupported` = a missing
   operator/feature (a *coverage* fix, usually bounded and certifiable);
   `Unknown` = the decision procedure ran and gave up (a *depth/budget* fix,
   usually harder). The scoreboard's per-row `Unsup`/`Unknown` split is the
   cheapest signal for where to aim.

## Recommended decide-rate order (grounded, not loudest-first)

1. **Strings coverage (QF_S/QF_SLIA `Unsupported`)** — Track 2. Biggest absolute
   win; each newly-supported operator is measurable on the committed slice.
2. **Uninterpreted-sort IR keystone (QF_UF)** — Track 1/2; the gap analysis notes
   it is *itself* dominance-eligible (a cheap IR change that also wins a row).
3. **Quantifier depth (e-matching/MBQI + quantified-BV)** — Track 1 keystone
   (e-graph + CDCL(T)) then Track 2.
4. **NIA before NRA** — `iand`/bounded NIA (`Unsupported`/budget) is more
   tractable than NRA CAD depth.
5. **NRA CAD depth — last**; honest `unknown` is acceptable parity here.

**Every step is gated by the same discipline:** re-measure the committed
SCOREBOARD slice (decide% must move, `DISAGREE` must stay 0), and — for `unsat`
gains — extend the proof/cert coverage so the Lean ledger does not regress.

## How to keep this honest

- This ranking is a snapshot of the **measured 35 baselines**; the true Z3/cvc5
  surface is larger. Growing the *number of measured divisions* (via the
  `bench --backend solver` keystone) is itself decide-rate-frontier work — an
  unmeasured division is an unknown gap, not a closed one.
- No decide-rate claim moves without re-running the scoreboard. "Supported an
  operator" ≠ "decide% rose" until the corpus says so.

*Owned by the engine/theory tracks (Track 1/2). The consumer track does not move
these numbers; its role is demand-pull + certifying value (it filed U6/U7/U8).*
