# ADR-1936: A gap census reports `attempts=`, and an unfinished dispatch is UNCLASSIFIED

Status: accepted
Index-summary: A blocker census must report `attempts=` per file and mark any row whose dispatch did not reach the end of the ladder UNCLASSIFIED, never by its give-up reason.
Index-status: accepted
Date: 2026-09-12

## Context

[ADR-1927](adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
closed one half of this: a ladder rung's *fragment refusal* is a decline, not
the query's verdict, and a census taken through a ladder that stops at its first
refusal measures the ORDER OF THE LADDER. Its correction moved `AUFDTLIRA`'s top
blocker from 174 of 200 to 3 of 200.

The other half surfaced in `QF_LIA` on 2026-09-12
([census](../../../bench-results/qf-lia-gap-census-20260912/README.md),
[note](../03-measurements/qf-lia-the-second-dispatch-rung-ate-the-budget-2026-09-12.md)).
A rung did not refuse — it **hung**. `term_identity::identity_normal_form`, the
second rung of `check_auto`, is an exponential tree walk over a shared `ite`
DAG; it takes no deadline and records no route attempt. On 23 of the division's
55 addressable files it consumed the entire 24 s budget, the process watchdog
killed the worker, and the file's recorded reason became "watchdog fired".

Every instrument agreed and every instrument was describing the dispatcher:
the route trail said `attempts=2` of a 16-rung ladder, the phase breadcrumb said
`stack=none`, and the give-up line said `Watchdog`. Nothing in any of those
three lines says "this census row is not about this query" — you only learn it
by comparing `attempts=` to the ladder length, which is one field that was
already being printed and was not being read.

Both halves produce a census that is reproducible, stable across samples, and
confidently wrong, so a rule that catches only the refusal half is a checker
that cannot fail on the hang half.

## Decision

**A blocker census over an addressable gap reports `attempts=` per file, and any
row whose dispatch did not reach the end of the ladder is reported as
`UNCLASSIFIED`, never by its give-up reason.**

Concretely, for any census, sweep, or parity note that ranks reasons:

1. Record `attempts=` (from `--trace`'s `; route` line) for every file, and
   record the ladder length the division's dispatch reaches when it completes.
2. A file whose `attempts` is below that length is `UNCLASSIFIED`. It may be
   counted, it may be broken out by which rung it stopped at, and it must not
   be added to a capability bucket or used to rank what to build.
3. A file with **no route trail at all** is its own row (here: killed during
   INGEST, which `--timeout-ms` does not bound), not an absence.
4. The corrected census — the same population re-run once the stopping rung is
   fixed — is the one that plans work. The uncorrected one is published beside
   it as evidence, not replaced by it.

`UNCLASSIFIED` is the load-bearing word. Reporting the give-up reason of a
dispatch that did not finish is what turns a rung's name into a division's
"top blocker".

## Consequences

- Every existing census whose method did not check `attempts=` is suspect in
  proportion to how early its dispatch stops. In `QF_LIA` that was 30 of 55
  rows; in `AUFDTLIRA` (ADR-1927) it was 174 of 200.
- The rule costs one column. `attempts=` is already in `--trace`'s `; route`
  line and needed no new instrument.
- It does **not** say a census must be preceded by a fix. It says the rows a
  stopped dispatch produced cannot be ranked. A census that is 100 %
  `UNCLASSIFIED` is a complete and useful finding — it names the rung to fix.
- It composes with the phase breadcrumb (`8860e2a60`): `attempts=` says the
  dispatch stopped, `stack=`/`deepest=` says where, and when the breadcrumb says
  `stack=none` the phase is code carrying no frame — which is a finding about
  instrument placement and is reported as such.

## Alternatives considered

- **Require every rung to be deadline-aware instead.** That is the right
  engineering target and is being pursued one instance at a time (four found so
  far), but it cannot be a precondition for measuring: the way you *find* the
  next deadline-blind rung is by taking a census and noticing the rows are
  unclassified. Making the measurement rule depend on the fix inverts the order.
- **Treat a watchdog kill as its own bucket and rank it.** This is what the
  board already does, and it is exactly the trap: "watchdog kill" is a fact
  about the harness. 149 watchdog kills board-wide have so far yielded 2
  converts in `QF_UFLRA` and 1 here, because the bucket is not a cause.
- **Drop unfinished rows.** An absent row and a strong negative must not render
  the same way. `UNCLASSIFIED` keeps the denominator honest.