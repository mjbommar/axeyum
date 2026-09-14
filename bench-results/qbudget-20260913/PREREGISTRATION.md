# Pre-registration — lane `QBUDGET`, 2026-09-13

Written and committed **before this lane ran the solver even once**. Everything
below is derived from code reading and from the committed TSVs of the previous
lane (`bench-results/ufnia-uflia-census-20260913/census/*.tsv`), which are that
lane's measurement, not this one's.

Branch point: `c73eb8adf` (local `main`). Every number this lane measures is
measured on **this branch**, not on `main`.

## 1. The budget architecture (established from code, not inferred from traces)

Two budgets appear in the UFLIA/UFNIA give-up strings, and they are **sibling
slices carved out of one nested deadline**, not the same clock.

The single root clock is the caller's `SolverConfig::timeout` (24 s on the
boards), turned into one `deadline: Option<Instant>` that
`finish_quantified_solve` (`crates/axeyum-solver/src/auto.rs:405`) threads
through every rung. Each rung calls `config_with_remaining_timeout(config,
deadline)` (`auto.rs:210`), which re-derives *what is left of the root clock*,
and then some rungs cut a `LadderSlice` out of that remainder. So the clocks are
nested (every slice lies inside the root deadline) and one rung's slice is a
sibling of the next rung's.

The quantified ladder, in order, with the share of the **then-remaining** clock
each rung may spend:

| # | rung | slice of remaining | constant |
|---|---|---|---|
| 1 | `q:forall-exists-witness` | all | — |
| 2 | `q:finite-expansion` | all | — |
| 3 | `q:uf-fmf-probe` | `uf_fmf_probe_budget` | — |
| 4 | `q:mbqi-quick` (first refusal) | **1/8** | `MBQI_FIRST_REFUSAL_SLICE` |
| 5 | `q:egraph` | **all** (default) | `quant_egraph_budget`, `QuantEgraphReservePolicy::WholeBudget` |
| 6 | `q:mbqi` | all | — |
| 7 | `q:uf-fmf-full` | all | — |

- **"quantified solve time budget exhausted after e-matching"** is
  `quantified_timeout("e-matching")` (`auto.rs:309`), emitted at `auto.rs:544`
  when rung 5 declined and `config_with_remaining_timeout` then found **nothing
  left of the root clock**. It is the ladder's sink for "the root deadline
  passed inside rung 5".
- **"e-matching: instantiation time budget exhausted"** is `egraph_timeout()`
  (`qinst_egraph.rs:2698`), the e-graph instantiation loop hitting **its own
  slice**, which is strictly inside the root deadline. A row carrying this
  string as its final give-up therefore **still had root clock left** when it
  stopped — and the census data confirms it: median `24000 − wall_ms` is
  **8,681 ms** (UFNIA) and **2,574 ms** (UFLIA) on the winnable rows.

## 2. Which rung emits the second string, and why it is not rung 5

Rung 5's `Unknown` is **declined**, not returned
(`run_egraph_quantified_fallback`, `auto.rs:345-358`). So a final give-up
carrying the e-graph's own string cannot be rung 5's. It is **rung 6**:

    prove_unsat_by_mbqi_inner            auto.rs:9582
      -> (shape guard fires; 5 sites: auto.rs:9613,9620,9630,9638,9654)
      -> prove_unsat_by_ematching        auto.rs:9976
        -> skolemized_egraph_retry       auto.rs:10126
          -> prove_quantified_unsat_via_egraph   <- the SAME loop as rung 5,
                                                    on the SKOLEMIZED assertions
          under QINST_EGRAPH_RETRY_SLICE = fraction(1/2)   auto.rs:4655

and `prove_unsat_by_ematching`'s last match arm (`auto.rs:10113`) makes the
loop's own decline win over the shape message, so `egraph_timeout()`'s string is
what rung 6 returns and what the front door prints.

The census's own `bound_by` column agrees with this reading and not with the
"rung 5 is the whole story" reading: on the 37 UFNIA rows in this family
`bound_by` is **`q:mbqi` on 27** and `q:egraph` on 10.

**So the e-graph instantiation loop runs TWICE on these files** — once at rung 5
on the original assertions, once inside rung 6 on the Skolemized ones — and
between them they are what spends the clock.

## 3. The starvation question, and why ADR-1970's ceiling is not one-way

[ADR-1970] measured a **reserve** on rung 5 (`AXEYUM_QUANT_EGRAPH_RESERVE`,
ships OFF) at its `share = 1` ceiling, which hands rungs 6-7 essentially the
whole budget, and got **+2 UFNIA / +0 UFLIA**. It called that a *sound one-way
ceiling*: "a file it does not decide is out of reach of every reserve."

That inference has a hole, and section 2 is the hole. The clock the ceiling arm
moved off rung 5 went to rung 6 — **which hands half of it straight back to the
same e-graph loop**. The ceiling arm therefore did not measure "the lower rungs,
fully funded"; it measured "the e-graph loop, with its two passes' budgets
re-proportioned." That is a real experiment and its null is real, but it is a
null about *where inside the e-graph family the clock sits*, not about whether
that family is the only rung able to decide these files.

**This lane does not re-run that experiment.** It asks the question the census
data raises and ADR-1970 did not test: the family in section 1's second row
**stops with root clock unspent**, and the reason is a 1/2 slice held back for
"the callers' later SAT-only stages" (`auto.rs:10124`) which, on UFNIA/UFLIA, are
`q:uf-fmf-full` — the pure-UF finite-model finder, which declines these
non-pure-UF divisions in one cheap scan and never spends the clock reserved
for it.

## 4. The lever, and why its ceiling arm IS one-way

`AXEYUM_QINST_EGRAPH_RETRY_SHARE` (new, ships OFF / value `2` = today's
behaviour). The measured arm is `1`: the Skolemized e-graph retry takes the
**whole remaining root clock**. No re-entry scheme, no reallocation and no larger
reserve can give that loop more time than the root deadline, so a file the arm
does not decide is out of reach of every budget policy on this rung at this wall
budget. That is the one-way property, and unlike section 3's it does not route
the clock back through the thing it took it from.

## 5. Pre-registered sizing

Sized on the **winnable** rows of this family only (18 UFNIA + 14 UFLIA = 32),
because a conversion rate measured on a MIXED blocker population does not
transfer to a subset of it. I therefore do **not** use ADR-1970's 2/46.

Effective budget multiplier for the retry loop, from the census walls:

| division | family n (winnable) | median stranded ms | retry budget today | under the arm | multiplier |
|---|---:|---:|---:|---:|---:|
| UFNIA | 18 | 8,681 | ~8.7 s | ~17.4 s | **~2.0x** |
| UFLIA | 14 | 2,574 | ~2.6 s | ~5.1 s | **~2.0x** |

(The multiplier is ~2x in both divisions by construction — the arm converts a
1/2 slice into the whole remainder. The divisions differ in how much *absolute*
clock that is, which is why I expect UFNIA to move more than UFLIA.)

**Prediction.** Doubling wall budget on already-failed SMT instances converts a
low single-digit percentage. I take 5 % for UFNIA (the larger absolute grant, and
the division where the retry is the binding segment on 27 of 37 rows) and 2 % for
UFLIA (a 2.6 s grant is small in absolute terms, and 11 of its 14 winnable rows
are bound by `q:egraph`, i.e. rung 5, which this lever does not touch).

    UFNIA  37 family rows x 5 %  ~= 1.9   ->  point estimate +2
    UFLIA  24 family rows x 2 %  ~= 0.5   ->  point estimate +0
    TOTAL over the 400 A/B files          ->  point estimate +2

**80 % bracket: [0, +5] net over 400 files.** Wilson, not normal.

**Decision rule, fixed now.** Net <= +1 after the 3x-per-arm re-check => I report
this as a **NEGATIVE RESULT**, recommend the lever ship OFF, and state plainly
that the clock-routing vein is closed for UFLIA/UFNIA and the next lane should go
at instantiation *selection*, not at the clock. Net >= +4 stable => propose
shipping, with the pure-UF control's movement on the same line.

**How this bracket could miss, named in advance.** (a) The two e-graph passes
share no state — the retry restarts from round 0 on the Skolemized set, and the
loop's cost per round grows superlinearly in accumulated ground terms, so the
*rounds* a 2x budget buys may be far fewer than 2x. If so the true conversion is
nearer 0 and I will be high, not low. (b) The census walls were measured under
the previous lane's ambient load; if the retry actually enters later than I
computed, the stranded clock is smaller and so is the grant.

## 6. Controls

- **`AUFLIA`** — the quantified control ADR-1970 already established is not
  vacuous on this route (`q:egraph` entered on 115/200 of it). It exercises the
  route and must not move.
- **`UF`** — added by this lane, and it is the control that can actually **lose**:
  it is the pure-UF division where `q:uf-fmf-full`, the rung whose reserve this
  arm spends, is the one that decides. If the 1/2 slice is protecting anything
  real anywhere, it is protecting it here. A null on `AUFLIA` alone would not
  have found that.

Both controls' movement is reported **even when it is zero**, with each one's
`q:egraph` hit rate beside it.

## 7. Envelope (identical to both pinned boards and to ADR-1970's A/B)

24 s wall, 8 GiB `ulimit -v`, one pinned **physical** core (`c,c+8`), wrapper
timeout 24+16 s. **One binary, two env values**, both arms back to back on the
same file on the same core, arm order alternating per file. Base arm runs under
`env -u AXEYUM_QINST_EGRAPH_RETRY_SHARE` — an environment with no lever in it,
not a lever set to its default.

**Lever polarity, stated explicitly:** the lever **ships OFF**. Unset, or `2`, is
today's shipped behaviour (1/2 slice). The **measured arm is `1`** (whole
remaining). The runner's header repeats this. A runner copied from this one that
does not flip the polarity measures the shipped arm against itself.

## 8. Noise floor

Measured, not assumed: one whole division (`UFNIA`), base arm, repeated 3x on the
same cores. Reported as the peak-to-trough band of the division total.

## 9. Second, unrelated finding already sized (the 0.1 s rows)

The 5 UFNIA rows dying at ~0.1 s on `ingest resource limit: 'distinct' with N
arguments requires M pairwise expansions; deterministic limit is 65536` are a
**front-door encoding** problem, not a budget problem, and 4 of the 5 are in the
winnable set. Diagnosis and the soundness constraint on the obvious fix are in
`DISTINCT-ENCODING.md` beside this file. Not A/B'd: these rows are deterministic
at 0.1 s, so "does it parse and decide" is the whole measurement and ambient load
cannot reach it.

[ADR-1970]: ../../docs/research/09-decisions/adr-1970-the-egraph-rung-eats-the-quantified-clock-to-decide-one-file-in-two-hundred.md
