# Pre-registration — ADR-2030 (lane `DECLINE-WIRING`)

Written and committed **before** either A/B ran. Branch base:
`git merge-base main HEAD` = `37ff18b568f414dc21e151c3a53292c40fb7fa71`, which
**was** local `main`'s HEAD when this lane branched.

## What is already known, and what is not

Two things below are **observations already in hand** when this was written, not
predictions. They are recorded here so the reader can tell which is which.

**Already observed (recorded, not predicted):**

1. **ADR-2020's defect 1 is refuted as stated.** ADR-2020 concluded that
   `combined.rs:86` hard-declines where its sibling at `auto.rs:4068` falls
   through, and that "the lazy fallback that already exists for the other caller
   is simply not offered to them". The ordered `ACKPROBE` log
   (`ackprobe-13.tsv`) shows the selector at `auto.rs:4068` engaging on
   **13 of 13** files behind those 17 replays, 5 to 145 times each. The lazy
   CEGAR route is offered, runs, and falls through *before* the query descends
   to the site that refuses it. What the census ranked at 21.8 % is the integer
   bit-blast width ladder consulting a **width-independent** admission test once
   per rung — 60 to 1,605 identical refusals per file — and reporting the last
   one as the query's verdict.
2. **One pilot file moved under the lemma-batch cap.**
   `UFLIA/simplify/javafe.ast.StandardPrettyPrint.322.smt2` returns `unknown`
   on the shipped arm and `unsat` at `AXEYUM_FC_LEMMA_BATCH_CAP=256`, agreeing
   with the file's declared `(set-info :status unsat)`. **One file is not a
   result.** It is why the full A/B below is worth running; it is not evidence
   for its outcome, and a single pilot on a population whose same-arm noise band
   is 1 of 129 (ADR-2020 R6) is exactly the size of the noise.

**Not known:** whether either lever moves the population, and in which
direction.

## The levers — polarity, stated once

Both are read through a `OnceLock` and **fail CLOSED**: unset, empty,
malformed, or zero returns the shipped constant.

| lever | OFF (shipped) | ON |
|---|---|---|
| `AXEYUM_BLAST_LADDER_ADMISSION` | unset | `1` — hoist the width-independent admission test out of the width-ladder loop |
| `AXEYUM_FC_LEMMA_BATCH_CAP` | unset | `256` — per-round ceiling on the lazy function-consistency lemma batch |

**The shipped arm is the one with the variable REMOVED** (`env -u`), not merely
unset, because the harness environment is inherited.

**Both arms are visible BY MECHANISM, asserted before measuring:**

* ladder hoist — the count of `ACKPROBE site=combined.rs:86` lines. Measured on
  `UFLIA/sledgehammer/QEpres/smtlib.1120322.smt2`: **736 OFF, 91 ON**.
* lemma cap — `FunctionConsistencyStats::summary` now prints
  `lemma_batch_cap=<n|off>`, the **effective** value. A variable that was
  ignored or mistyped prints `off`, which is the shipped value. Measured on
  `javafe.ast.StandardPrettyPrint.322.smt2`: `lemma_batch_cap=off,
  lemmas_added=12440` OFF; the ON arm decided before reaching a replay probe.

## Why 256, chosen from the distribution and not after the fact

The distribution of the batch is in `cegar-batch-distribution.md`, taken from
the committed ADR-2015 census — **31 observations, published in full before any
cap existed.** On every one of the 31, `lemmas_added == equal_arg_pairs`: the
batch is the entire equal-argument pair set, emitted the moment any single pair
is violated.

| field | min | p25 | med | p75 | p90 | max |
|---|---:|---:|---:|---:|---:|---:|
| `violated_pairs` | 0 | 0 | 8 | 47 | 229 | 3,120 |
| `equal_arg_pairs` = `lemmas_added` | 0 | 0 | 191 | 3,246 | 12,440 | 17,750 |

The amplification reaches **1,555x** (8 violated pairs → 12,440 lemmas).

**The rule, fixed before the value:** the cap must (a) admit the **full**
violated set on at least 90 % of observed rounds, so the pairs the candidate
model actually violates are never truncated — `violated_pairs` p90 is **229**,
so `cap >= 229`; and (b) bind on the flooded tail. **256** is the smallest
round value satisfying both, and it is the value of the only existing constant
of this kind in the same file (`MAX_PRESEEDED_FUNCTION_CONSISTENCY_LEMMAS`).
It binds on **15 of 31** observations.

Violated pairs are queued **first**; the remaining equal-argument pairs fill the
batch up to the cap. Pairs not emitted are **not** marked `added`, so they
remain available to the next round.

## Decision RULES (not a rate)

**No conversion rate is pre-registered, and none may be borrowed.** ADR-1980's
bracket missed by 3x because a rate measured on a MIXED blocker population was
carried to a subset. The 21.8 % in this lane's brief comes from exactly such a
mixed census and is used here only to identify a population, never to predict a
yield.

| | rule |
|---|---|
| **R1** | Report the two levers **separately**. Their populations are disjoint — `files-eager-ackermann` ∩ flooded = **0 of 13** — so a joint arm would confound them. |
| **R2** | Ship a lever only if it moves **>= 6 rows net**, every moved row **STABLE-GAIN**. Same threshold as ADR-2020 R4, for comparability. |
| **R3** | Re-run **every moved row 3x per arm**; classify STABLE-GAIN / STABLE-LOSS / UNSTABLE / FLIP. A row that is not 3-for-3 in one direction is UNSTABLE and does not count toward R2. |
| **R4** | Publish a **noise floor**: one whole division, byte-identical configuration, both passes. If the lever's effect is inside that band, **that is the result** and it is stated as such. |
| **R5** | A **control division that must not move** (`QF_BV`), reported at zero and shown **non-vacuous by route**, not by assertion. |
| **R6** | **Interleaved per-file**, arms back to back on the same file on the same pinned core, order rotating per file. **One binary, two env values.** |
| **R7** | **Shard configuration held FIXED across arms and stated**: both arms run *inside* each shard, so a shard can never move one arm relative to the other (ADR-2000). |
| **R8** | Every **new verdict** checked against three independent authorities — declared `:status`, z3 (`-T:` SECONDS), cvc5 (`--tlimit` MILLISECONDS). **The comparable denominator is printed beside any zero** (ADR-1957), no-opinion counts separate. |
| **R9** | **Wilson 95 %** for every small-n proportion. |
| **R10** | The A/B measures **THIS BRANCH**. State the merge-base and predict the post-merge value with a reason. |
| **R11** | Any check not finished is reported as **"did not run"**. Never an intention described as an observation. |
| **R12** | Freshness is licensed by a **rebuild that recompiled** (new binary mtime + a non-trivial compile time), not by exit 0. ADR-2020's guard fired twice; this lane's first build already skipped an edit and reported `Finished in 0.04s`. |
| **R13** | **Carry the message out** (ADR-1980's named prerequisite): where a rung converts another rung's refusal, the refusing rung's own sentence must reach whatever the ladder ends on, or the blocker census starts reading a different string. |

## Predictions, written down

* **Ladder hoist: 0 rows move.** It is verdict-preserving by construction —
  `check_with_all_theories` binds `width` only after the two reductions
  replicated in the hoist, so a refusal at any rung is a refusal at every rung.
  The only behavioural difference is *which* `Unknown` a caller sees. What it
  should buy is **wall clock** (60–1,605 discarded arena clones per file), and
  a **correctly attributed** give-up string. If wall clock returned to the
  instantiation loop moves a verdict, it moves in **either** direction —
  ADR-1995 established the loop's verdict is not monotone in its budget.
* **Lemma cap: unknown, and that is the point.** The pilot moved one row in the
  gain direction. The prediction on record is **< 6 net**, i.e. the cap also
  ships OFF, because six lanes before this one on this gap shipped OFF or
  nothing and all six were right to. If it exceeds 6 STABLE-GAIN, that
  prediction was wrong and the ADR will say so in those words.

## Shards — fixed, and stated

**This lane takes 4 pinned cores**, not the 6 the brief allows, so a concurrent
lane has room:

| host | cores | job |
|---|---|---|
| s5 | `1`, `3` | A/B-1 — ladder hoist, 129 rows, 2 shards |
| s6 | `1`, `3` | A/B-2 — lemma cap, 129 rows, 2 shards |

Controls and the noise floor run on the **same four cores** in a later phase,
never concurrently with the main arms. Budget 24 s, `ulimit -v` 8 GiB, both arms
inside each shard.
