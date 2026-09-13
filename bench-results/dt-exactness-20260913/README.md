# DT-EXACTNESS — the ADR-1966 check, and the sizing it produced

Lane `DT-EXACTNESS`, 2026-09-13. Branched from `main` at `c2fb0ade4`.

**This file is the lane's PRE-REGISTERED sizing. It is written and committed
before any solver code is measured**, so the bracket below cannot be adjusted
to whatever the A/B happens to produce. The measurement lands in `AB.md`
beside it.

## 1. The target as handed over

[ADR-1975] sized three refusals, all of which rest on
`datatype_expansion_is_exact` in `crates/axeyum-solver/src/datatype_native.rs`
— false exactly when a constructor field has sort `Datatype(_)`:

| refusal | ADR | UFDTLIRA | UFDT | AUFDTLIRA | UFDTNIRA | total |
|---|---|---:|---:|---:|---:|---:|
| congruence over a datatype ARGUMENT whose expansion is not exact | 1935 | 29 | 20 | 23 | 0 | **72** |
| a UF whose RESULT datatype's expansion is not exact | 1946 | 9 | 16 | 14 | 0 | **39** |
| a UF applied to a datatype term that is neither a free variable, a constructor application, nor another UF | 1920/1942 | 11 | 0 | 2 | 0 | **13** |
| **total** | | **49** | **36** | **39** | **0** | **124** |

Re-derived here from the committed census by `refused-rows.py`, which reads
`bench-results/ufdt-family-20260913/census/<div>.winnable.tsv` and matches the
three refusal sentences. It reproduces 124 exactly.

## 2. The ADR-1966 check — run first, as ADR-1975 required

> *"Run [ADR-1966]'s check on these three refusal sites first. A rung BELOW may
> own the construct, in which case the refusal should be a DECLINE and the fix
> is far smaller than a capability. **This is the cheapest thing to try and this
> lane did not try it.**"*

It was run, and **the answer is that the check has already been run, by
ADR-1966 itself, and the site it names is the one these three refusals travel
through.** Three separate things had to be established to say that:

### 2a. The mbqi rungs are ALREADY declines. The refusal is not terminal there.

All 124 rows carry a `mbqi declined an unsupported fragment: …` prefix, so the
obvious reading is that MBQI is the propagating rung. It is not. Both MBQI
rungs already convert an `Unsupported` into a decline:

- `auto.rs` `mbqi_first_refusal` — `Err(SolverError::Unsupported(message)) =>`
  records `unsupported_decline(&message)` and returns `Ok(None)`, falling
  through.
- `auto.rs` `finish_quantified_solve`'s full MBQI rung — the same `Err` arm
  becomes `CheckResult::Unknown`, with the comment *"MBQI refusing this query's
  FRAGMENT is not a verdict on the query"*, and the full pure-UF finite-model
  rung below it then runs.

So the sentence the census reads is the LAST `unknown` detail, not an
un-converted propagation. **At the quantified-ladder level ADR-1966's rule is
already applied.**

### 2b. The sentences come from `check_with_datatype_native`, reached through exactly one call site.

All three strings are produced inside
`crates/axeyum-solver/src/datatype_native.rs` — two by
`collect_ackermann_groups`' exactness checks, one by its argument-shape check.
`check_with_datatype_native` has two callers in the crate
(`grep -rn 'datatype_native::'`):

- `crates/axeyum-solver/src/datatype_elim.rs:43` — a tail call inside the
  datatype-elimination route, itself reached from the site below.
- `crates/axeyum-solver/src/auto.rs` `check_auto_dispatch` — **the site
  ADR-1966 names**, and until this lane a bare `?`.

MBQI's ground sub-solves go through `check_auto_dispatch`. So the refusal that
ends the ladder is manufactured at that `?`: the ground sub-solve dies as an
ERROR, MBQI reports the fragment refusal, and the thirteen dispatch rungs below
the datatype branch never ran **inside the sub-solve**.

### 2c. ADR-1966 measured that exact site and reverted it for a non-technical reason.

From `auto.rs`'s own comment at the site, and ADR-1966 §"The site that was not
taken, and exactly what blocks it":

> `check_auto_dispatch` → `check_with_datatype_native` is the textbook
> instance: thirteen rungs below it … The conversion was written, built and
> measured — **every `AUFDTLIRA` number in this ADR comes from it** — and then
> reverted.

**+22 files / −2 on `AUFDTLIRA` (90 → 110 of 200), 0 `sat`↔`unsat` flips, all
23 new verdicts confirmed `unsat` by z3 4.13.3 and cvc5 1.3.4.** It was
reverted because it turns 7 assertions in 4 registered pre-push suites red
(`dt_uf_gate`, `dt_capability_1935`, `dt_constructor_arg_1942`,
`dt_valued_result_1946`), and ADR-1966 named one prerequisite that removes 3 of
the 7: *carry the datatype rung's own sentence into the final `unknown` first*.

### The finding, stated plainly

**The ADR-1966 check comes out POSITIVE, and it is the cheaper fix.** These
three refusals do not need a recursive tag/field expansion to move. They need
the dispatcher to stop treating a route's refusal as the query's verdict. The
capability question — a recursive expansion for the 97 nested-not-recursive
files — is a *separate and still-open* target, and this lane does not touch
`datatype_expansion_is_exact`, `field_sort_expands`, or any encoding.

**What this is not.** The exactness guards stay exactly where they are and fire
on exactly the same queries. An inexact tag/field expansion is still never
emitted, so the wrong `unsat` [ADR-1930] shipped is still impossible by
construction. Only the DISPATCHER's handling of the refusal changes.

## 3. The pre-registered sizing bracket

**Upper bound (trivial):** 124. Every refused row could in principle be decided
by a rung below. Nothing supports that and this project's own tally
(143→6, 51→2, 173→10, 84→49, 27,150→1,135, 19,620→0, 177→0, 934→0, 46→2) says a
blocker count is not a reachable count.

**Point estimate, derived rather than guessed.** ADR-1966 measured this exact
conversion on one division. Its refusal population on `AUFDTLIRA` was the four
ADR-0022 refusals at 70 + 32 + 13 + 1 = **116 blocked rows**, and the
conversion yielded **+22 confirmed gains**. That is a measured conversion rate
of **22 / 116 = 19 %** — the only rate anyone has for this change.

Applied to this lane's 124: **124 × 19 % ≈ 23 files**.

**The bracket this lane pre-registers: 8 to 35 files across the three
divisions, point estimate 23.**

Two reasons the realised number can land below the point estimate, both stated
now rather than after the fact:

1. **ADR-1966's 22 came from a superset.** Its 116 rows include the
   array-of-datatype FIELD refusal and the surviving-datatype-term refusal,
   which this lane's 124 excludes. If the gains concentrate in those, the
   exactness rows convert at a lower rate.
2. **`AUFDTLIRA` has moved from 90 to 96 of 200** since ADR-1966's A/B
   (`bench-results/postmerge-board-20260913/`). Six files of that headroom are
   already taken by other lanes' work, and some of the +22 may be among them.

One reason it can land above: `UFDTLIRA` and `UFDT` were **never measured** for
this conversion. ADR-1966 ran `AUFDTLIRA` only.

**This lane commits to reporting the realised number against this bracket,
whichever side it falls on, and to reporting it as a BRANCH measurement with an
explicit expectation for its post-merge value.**

## 4. Polarity, and what it means for the ceiling

From ADR-1975's census: `UFDT` 50 unsat / 1 sat, `AUFDTLIRA` 80 unsat / 0 sat,
`UFDTLIRA` 53 unsat / **23 sat**. A decline conversion is polarity-neutral —
the rungs below include both the refutation family and the finite-model
finders — so unlike a refutation-only fix this does not ceiling at 53 on
`UFDTLIRA`. ADR-1966's own blocked tests are evidence for the `sat` half: four
of the seven go red precisely because the front door starts returning
`Ok(Sat(model))` where it used to return `Err`.

## 5. Files

- `refused-rows.py` — re-derives the 124 from the committed census. Prints the
  per-division split and writes `<div>.refused.tsv`.
- `AB.md` — the measurement. Written after, never edited to match this file.

[ADR-1930]: ../../docs/research/09-decisions/adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md
[ADR-1966]: ../../docs/research/09-decisions/adr-1966-a-rungs-refusal-of-a-construct-a-later-rung-owns-is-a-decline.md
[ADR-1975]: ../../docs/research/09-decisions/adr-1975-valid-universal-elimination-spends-24-seconds-to-prevent-a-107-millisecond-refutation.md
