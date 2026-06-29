# Decide-rate frontier — where the Z3/cvc5 parity gap actually is (2026-06-28)

> **Measured follow-up (2026-06-29):** the *accessible* (curated) corpus slices
> are re-measured in [decide-rate-measured-2026-06-29](decide-rate-measured-2026-06-29.md).
> Key correction: on accessible data **QF_S is already at z3 parity (56/56)** —
> the string `max_len` lever has no verifiable headroom there — while **QF_UF
> lagged z3 by 4 (37/48 vs 41/48)**, localized to theory-combination routing +
> uninterpreted-sort `ite`/Ackermann. **Landed since:** a `check_auto`
> robustness fix (never hard-error on a valid QF_UF instance) + equisatisfiable
> uninterpreted-sort `ite`-elimination for the e-graph path → **QF_UF 37 → 39**
> (gap to z3 −4 → **−2**), DISAGREE = 0. Remaining QF_UF gap = UF+theory
> combination routing (the keystone).
>
> **Also landed (QF_ABV):** robustness (no hard-error on a wide-index array
> equality) + **write-index array extensionality** (decides shared-base
> `store-chain = store-chain` over 32-/64-bit indices without `2^iw` enumeration)
> → **QF_ABV 173 → 176/177** (gap to z3 **−1**), DISAGREE = 0,
> `abv_differential_fuzz` clean.

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
| 1 | **QF_S** (strings) | 134 | 44% | ~75 | `Unsupported` (62) | **encoding/depth** (bounded length ≤16 + unbounded regex) |
| 2 | **QF_UF** bounded | 82 | 54% | ~38 | `Unsupported` (24) + `Unknown` (13) | coverage (uninterp sorts) + depth |
| 3 | **QF_SLIA** | 50 | 30% | ~35 | `Unsupported` (29) | **encoding/depth** (bounded strings + int) |
| 4 | **QF_NRA** cvc5 | 38 | 24% | ~29 | `Unknown` (27) | **depth** (CAD) |
| 5 | **QF_NIA** cvc5 | 39 | 54% | ~18 | `Unknown` (10) + `Unsupported` (8) | depth + coverage |
| 6 | **BV** quantified | 54 | 69% | ~17 | `Unsupported` (11) + `Unknown` (6) | quantified BV |
| 7 | quantified **LIA / UF** | 17 | 0% | ~17 | `Unsupported`/`Unknown` | quantifier coverage |
| — | QF_SEQ, QF_AUFBV(cvc5), QF_AUFLIA, QF_FF, QF_UFLIA tails | — | 56–80% | ~30 | mixed | near-strong tails |

> **Correction (grounded in `crates/axeyum-solver/src/strings.rs` +
> `capabilities.rs`):** a high `Unsupported` count does **not** automatically mean
> "missing operator." axeyum's string theory already implements nearly the full
> SMT-LIB string surface (`str.++/len/at/substr/indexof/replace/replace_all/
> prefixof/suffixof/contains/to_int/from_int/to_code/from_code/to_re/in_re/
> replace_re*`). Its `Unsupported` comes from the **bounded** encoding: strings are
> a `(len, content)` pair with **`max_len ≤ 16`** (content ≤ 128-bit BV) and a
> bounded regex fragment — so instances needing **longer strings or unbounded
> regex (Kleene star) fall out of fragment**. *Always check the cause, not the
> count.*

## The strategic read (what this says)

1. **Strings are the single largest decide-rate gap by count (~117 across
   QF_S/QF_SLIA/QF_SEQ), but it is a *depth/encoding* gap, not a cheap coverage
   win.** The operators exist; the bound (`max_len ≤ 16`, content ≤ 128-bit) and
   the bounded-regex fragment are the wall. Two routes, both real Track-2 work:
   (a) **raise the bound** — widen `content` past 128-bit (wider BV → bit-blast
   cost grows, so pair with reduction/SAT-core wins); cheap to try, bounded
   payoff; (b) **an unbounded/length-aware string DP** (the cvc5/Z3 approach) —
   large effort, the real fix. *Measure route (a) first* (it's a config/encoding
   change) before committing to (b).
2. **QF_UF (~38)** is the more tractable lever: it splits *coverage*
   (uninterpreted-sort handling — the `overbound-uninterp-sorts` rows sit at
   0–67%) and budget (`Unknown`). The **first-class uninterpreted-sort IR
   keystone** is flagged in the gap analysis as *itself dominance-eligible* — a
   cheap IR change that wins a row. Likely the best ROI on this list.
3. **QF_NRA (~29) is the genuine 15-year catch-up** — `Unknown`-dominated = CAD
   depth (`nra_degree` frontier = 2). High effort, low near-term ROI; *do not*
   spend the decide-rate budget here first. Match Z3's *practical* rate, accept
   honest `unknown`.
4. **Quantifiers (BV/LIA/UF quantified ≈ 34 undecided, several rows at 0%)** are a
   coherent cluster — the e-matching/MBQI + quantified-BV path needs depth. Tied
   to the **e-graph + CDCL(T) keystone** (Track 1, P1.4/P1.5).
5. **`Unsupported` vs `Unknown` is the triage axis, but verify the cause.**
   `Unsupported` *usually* = a missing feature, but (per the correction above) can
   also mean "outside a bounded fragment." `Unknown` = the decision procedure ran
   and gave up (depth/budget). Read the actual rejected instances, not just the
   count.

## Recommended decide-rate order (grounded, corrected)

1. **Uninterpreted-sort IR keystone (QF_UF, ~38)** — Track 1/2; the gap analysis
   notes it is *itself* dominance-eligible (a cheap IR change that also wins a
   row). Best ROI / effort on this list.
2. **Strings — try the cheap encoding lever first (QF_S/QF_SLIA, ~110):** raise
   `max_len` / widen `content` and *re-measure* before deciding whether the larger
   unbounded-string DP investment is warranted. Biggest count, but a depth gap.
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
