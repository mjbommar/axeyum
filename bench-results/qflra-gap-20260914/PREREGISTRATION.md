# QFLRA-GAP — pre-registered rules

Lane `QFLRA-GAP`, 2026-09-14. Branched from `main` at `cfcae7fa78bbc8297ccb62d8517895edb87d8c33`;
`git merge-base main HEAD` **is** that SHA, which **is** local `main`'s HEAD.

**This file is committed BEFORE the census completes and BEFORE any lever
exists.** At the moment of writing, 43 of 200 census rows had been produced and
none had been aggregated. Nothing below can be tuned to a result.

The one thing already known when this was written, because it fell out of a
three-file smoke run, is recorded here so it cannot later be presented as a
prediction: **the board's 40 `none` rows are out-of-memory aborts**
(`rc=134`, `memory allocation of N bytes failed` on stderr, ~7.8 GiB RSS
against the harness's 8 GiB `ulimit -v`), not timeouts. The rules below were
written knowing that and not knowing how many rows it covers, whether any of
those rows are addressable, or whether anything moves them.

## R0 — the population is re-derived, never inherited

[ADR-2035] found **8 of 22** censused "declining" files were decided anyway.
Every number in this lane's report comes from a run of the CURRENT tree's
binary (`smtcomp_cli-cfcae7fa7`, sha256 `ea0fceaf55a562e6…`) on the canonical
200-file `QF_LRA` board list. The 2026-09-14 board TSV is used only to state
what was previously believed, never as a population.

## R1 — the census splits causes BEFORE counting, and by four channels not one

A give-up string that covers more than one site must be split and re-censused.
Four cause channels exist in this binary and **only the first is a give-up
string**:

1. `; give-up kind=… detail=…` on stdout;
2. the verdict line;
3. the process exit status (`134` = abort, `124` = wall kill);
4. **stderr** — an allocation failure prints ONLY here and emits **no
   `; give-up` line at all**.

A census built on channel 1 alone loses channel 4 entirely. The runner
captures all four plus the full `; route-trail` JSON per file and keeps every
raw log, so the census can be re-split without re-running.

Two splits are pre-committed as required, because both labels are known to
cover more than one site:

- **`kind=Timeout` is compound.** `auto.rs` relabels a reduced solve's own
  `Unknown` as `preprocessed dispatch timeout after reduced solve; the reduced
  solve's own reason was [{kind}] {detail}`. The detail **contains `;`** — the
  exact [ADR-2020] separator trap. Every `Timeout` row is split on its INNER
  `[{kind}] {detail}`, and the inner reason is what is counted. A row is
  reported as a clock only when it has no inner reason.
- **`bound_by` is taken from the route trail, not from the give-up text.** A
  give-up sentence names the route that produced the sentence; the trail names
  which rung the ladder actually stopped at and how many rungs ran
  (`attempts=`). [ADR-2045's own note] an early rung that refuses becomes the
  answer, so `attempts=` is checked against ladder length before any bucket is
  called a blocker.

Any bucket that survives this and still covers more than one site is split
again and the report says so.

## R2 — refusals and exhausted clocks are separated and reported with wall time

Every bucket is reported as `n`, median ms, and the share at ≥ 90 % of the
24 000 ms budget. A bucket whose median is a small fraction of the budget is a
REFUSAL and is reported as one; only a bucket sitting at the budget is an
exhausted clock. Counts without this split are not published.

## R3 — the addressable set is defined by the references, on the current tree

A row we do not decide is **addressable** only if z3 or cvc5 decides it at the
same 24 s budget on the same host class. `z3 -T:` takes SECONDS, `cvc5
--tlimit` takes MILLISECONDS. Rows nobody decides are reported separately and
are never counted toward a prize.

## R4 — the A/B is one binary, two env values, interleaved per file

If anything is built: arms run back to back on the **same file**, on the
**same pinned core**, order alternating per file, from **ONE binary** under
two environment values. Polarity is stated in the runner header. The arm
measures THIS BRANCH; the report predicts the post-merge value and gives the
reason.

## R5 — every moved row is re-run 3× per arm, against a measured noise floor

Classification: **STABLE-GAIN** (3/3 decided in the arm, 0/3 in base),
**STABLE-LOSS** (the converse), **UNSTABLE** (anything between), **FLIP** (a
verdict that changes identity, not just presence). A noise floor is measured
on one whole division, same arm, repeated, and published as a count. **The
band is assumed non-zero until measured.**

## R6 — the control division must be shown NON-VACUOUS

A control is named only after checking, from its own route trails, which route
binds its undecided rows and that the route **executes** there and does not
consult `memory_budget::current_limit_bytes`. [ADR-2035]'s control was vacuous
and its measurement said so. **`QF_BV` is disqualified as a control in
advance**: `MemoryBudget::clause_ceiling` divides the limit by
`ENCODING_BYTES_PER_CLAUSE = 384`, so any memory limit binds the bit-blast
route directly. `QF_BV` is measured as an EXPOSURE division instead — a place
the change can only cost us.

## R7 — new verdicts are verified against three authorities, denominator published

`:status`, z3, cvc5, via `bench-results/dt-exactness-20260913/verify-new-verdicts.sh`.
No-opinion counts are reported separately and the **comparable denominator is
printed beside any zero** ([ADR-1957]). A `sat` is additionally evidenced by
model replay, not by reference agreement — a sat-side reference control is
vacuous ([ADR-1976]) — and [ADR-2010]'s limitation (the front door's replay
does not cover parser-level rewrites) is stated wherever replay is cited.
Wilson intervals for small `n`.

## R8 — the ship rule

A lever ships **`On`** only if, on `QF_LRA`, the interleaved A/B shows

- net **≥ +5** files, and
- **0** STABLE-LOSS, and
- **0** FLIP, and
- **0** authority disagreements at a non-zero comparable denominator, and
- the control division at **0** with its non-vacuity shown, and
- the exposure division (`QF_BV`) at net **≥ 0**.

Otherwise it ships **`Off`** and the ADR reports the refutation. Eleven lanes
shipped `Off` or refuted their own premise this week and every one was right
to. **A conversion rate measured on a MIXED blocker population is not
transferred to a subset** ([ADR-1980], [ADR-2030]): each bucket's rate is
measured on that bucket or it is not claimed.

## R9 — the correctness claim is separated from the verdict claim, in advance

If the census confirms that a material share of this division dies by
**process abort with no verdict**, then that is a defect in its own right and
its merit does **not** depend on R8's count:

- `unknown` is a first-class result and a Hard Rule; an abort is not a result
  at all. `smtcomp_cli`'s own source already calls an abort "strictly worse
  than the first-class `unknown`".
- a competition harness that bounds memory externally gets **no verdict, no
  reason, and a core dump** where the solver could have declined in good order
  and let later rungs run.

This is pre-registered so that a null R8 cannot be retro-fitted into a
correctness win, **and** so that a null R8 cannot be used to dismiss a real
correctness defect. They are reported as two findings with two verdicts.

## R10 — what would falsify the whole hypothesis

Stated in advance so the negative is publishable:

- if the abort bucket is small (< 10 rows on the re-derived population), the
  memory story is not this division's problem and the census must name the
  binding cause instead;
- if the abort rows are ones **no** reference solver decides, converting them
  to `unknown` buys **zero** board files and R8 fails by construction — the
  correct outcome is then R9 alone, shipped as a contract fix with an honest
  `+0`;
- if setting the limit makes the admission screens refuse work that currently
  SUCCEEDS, the arm shows losses and the lever ships `Off`.
