# Strings re-measurement — 2026-07-29

Closes the question posed in
[`agent-program-2026-07-28/README.md`](agent-program-2026-07-28/README.md) §1,
fact 2: the committed SCOREBOARD reads 36 % QF_SLIA while lane work reported
100 % on Noetzli, and *"until they are [re-measured], we do not know what strings
actually cost us."*

They have now been re-measured. The answer is not the one the program assumed.

## Method

Each row was re-run at **the exact committed baseline config**, read out of the
baseline artifact rather than reinvented: `--backend solver --rewrite off
--compare-z3 --timeout-ms 10000 --jobs 4`, same corpora, release build. Every row
was then measured a **second** time at `ffc466b4` — the pre-Phase-0 commit — to
attribute any movement.

Evidence: [`bench-results/strings-remeasure-20260729/`](../../bench-results/strings-remeasure-20260729/)
(six artifacts, current `main` and `ffc466b4` for each row).

## Result

| Row | Committed SCOREBOARD | Current `main` | `ffc466b4` | Δ vs committed |
|---|---|---|---|---:|
| QF_SLIA | 18 / 50 (36 %) | **25 / 50 (50 %)** | 25 / 50 | **+7** |
| QF_S | 87 / 134 (65 %) | **93 / 134 (69 %)** | 93 / 134 | **+6** |
| QF_SEQ | 26 / 33 (79 %) | **22 / 33 (67 %)** | 22 / 33 | **−4** |

Net **+9 decisions** against the committed record.

## The two findings that matter

**1. The committed baselines are stale in both directions.** QF_SLIA and QF_S
understate the solver by 7 and 6 decisions; QF_SEQ *overstates* it by 4. A stale
generated view is not automatically conservative — the QF_SEQ row has been
claiming decisions the code no longer makes.

The four lost QF_SEQ decisions are all `unsat` (5 → 1) and all land in the
`bounded-string unsat not confirmed bound-independent (P2.7 A.2 gate)` blocker.
That is a soundness-motivated decline, so the *behaviour* is defensible; what is
not defensible is that the committed number never followed it.

**2. Phase 0's strings work moved these rows by exactly zero.** Every row is
**identical** at `ffc466b4` and at current `main`. The Noetzli mechanisms that
took the fixed 1,880-file population to 1,880/1,880 changed nothing on the
curated cvc5-regress slices.

That directly contradicts the working assumption behind Lane B. The gains
recorded above were already in the code before Phase 0 and had simply never been
measured; the regression likewise predates it. The honest read is that the
Noetzli work is **population-specific**, and no claim about it should be
generalised to QF_SLIA/QF_S/QF_SEQ without a measurement on those slices.

## Why the baselines were NOT updated

The fresh artifacts are committed as dated evidence, **not** promoted into
`bench-results/baselines/`, because doing so would write a false disagreement
into the authoritative scoreboard.

Re-measuring QF_S raises `SOUNDNESS ALARM: primary backend disagrees with Z3
oracle` on `r1_QF_SLIA_pattern1.smt2`, and regenerating from it puts
**DISAGREE = 1** in the QF_S row — breaking the `DISAGREE = 0 everywhere`
headline. Adjudicated directly: the declared `:status` is `sat`, and the
standalone **z3 binary**, **cvc5 1.3.4**, and **axeyum** all answer `sat`.
**Axeyum is correct and the alarm is false.**

The cause is a harness boundary defect, tracked separately. The in-process oracle
recorded `outcome: "unsat"` with `solve_ms: 0` and `translate_ms: 0`. The z3
backend declines `Seq`/regex before translation, so it never saw the string
problem — it was handed the **bounded packed-BV encoding** (ADR-0029). This
benchmark needs `x` to match `"pref"` followed by `a`…`z` in order, so any
satisfying string exceeds 30 characters, far past the bounded length cap: the
encoding really is unsat while the original really is sat. Axeyum answers the
original semantics; z3 answers the encoding; the harness compares them as though
they were the same query, under the misleading label
`query_boundary: "original parsed assertions"`.

Note also that `summary.disagree` read **0** while
`triage.soundness.oracle_disagreements` read **1** — a content grep of the
summary line alone would have missed this entirely.

**Promoting these rows into the baselines is blocked on fixing that boundary.**
False alarms are the benign direction; the same defect can equally produce false
*agreement* that masks a genuine bug, which is why it is worth fixing before any
string row is re-baselined.

## Next

1. Fix the oracle boundary: decline rather than compare when the query reaching
   the in-process oracle is a bounded-string encoding, or route string logics to
   the external z3 binary (which reads the original text); and propagate
   `oracle_disagreements` into `summary.disagree` so an alarm cannot be dropped.
2. Re-run these three rows and promote them into `bench-results/baselines/`,
   regenerating `SCOREBOARD.md`.
3. Re-scope Lane B against this data rather than against the Noetzli figure. The
   residual is now known: QF_SLIA 21 unsupported + 4 unknown, QF_S 32
   unsupported + 9 unknown, QF_SEQ 10 unknown — and the QF_SEQ unknowns are
   concentrated in the A.2 bounded-unsat gate, which is a concrete mechanism to
   attack rather than a diffuse gap.
