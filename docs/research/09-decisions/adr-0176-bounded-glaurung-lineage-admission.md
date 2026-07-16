# ADR-0176: Bounded Glaurung lineage admission

Status: accepted
Date: 2026-07-15

## Context

ADR-0171 accepts Glaurung's explicit per-path warm Axeyum integration as an
opt-in performance path, but leaves it ineligible for broader admission because
retaining one arena/AIG/CNF/SAT session per live explorer path raises process
RSS by 6.3%--31.0%. Glaurung `49f1fe2` supplies atomic live-session and
per-snapshot assertion ceilings with deterministic one-shot fallback, but its
unset ceilings are effectively unbounded. ADR-0175 makes AIG construction
cheaper and establishes the baseline on which those limits must be calibrated.

This is downstream workload and integration evidence. It does not move
Glaurung policy into Axeyum's trusted solver, weaken original-term model replay,
change proof checking, or make warm reuse automatic.

## Decision

Admit a measured bounded default inside Glaurung's still-explicit lineage mode:
retain at most nine live path sessions and at most 128 assertion roots per path.

- Either ceiling remains explicitly overrideable by a decimal environment
  value; invalid values continue to fail closed as zero.
- A check that would exceed a ceiling uses the ordinary one-shot Axeyum path.
  An already-retained over-limit owner is closed first.
- Every fallback reason and both configured ceilings are printed with the warm
  lifecycle counters.
- No solver verdict is cached. SAT still requires model replay against the
  original assertions, UNSAT retains the existing evidence boundary, and
  `Unknown` remains distinct from an error or UNSAT.
- `GLAURUNG_AXEYUM_WARM_REUSE=lineage` remains required. This decision does not
  authorize an implicit GQ9 warm policy.

## Evidence

The accepted v4 profiles first establish the structural envelope. Assertion
counts peak at 123 roots on `win10-vwififlt`, 78 on Dptf, and 51 on IntcSST;
live sessions peak at 11, 5, and 11 respectively. An assertion ceiling of 128
therefore covers every established occurrence without fallback while providing
a deterministic guard beyond the measured tier.

A coarse live-session sweep on the ADR-0175 binary rejects four: vwififlt sends
1,934/4,753 checks one-shot and Axeyum rises to 7.755 seconds. Eight lowers RSS
but sends 145 vwififlt checks one-shot and gives up most of the same-stream Z3
lead. Twelve is behaviorally identical to unbounded. Nine is the measured knee:
45/4,753 vwififlt and 4/1,672 IntcSST checks fall back; Dptf never reaches it.

Three order-balanced cap-9/cap-12 rounds on each driver decide and agree all
20,958 checks per policy with zero assertion fallbacks, unknown splits, resets,
or finding changes.

| Driver | Cap-9 Axeyum mean | Cap-12 mean | Median RSS, cap 9 -> cap 12 | Path fallbacks per run |
|---|---:|---:|---:|---:|
| `win10-vwififlt` | 4,465.6 ms | 4,466.7 ms | 125,812 -> 136,804 KiB | 45/4,753 |
| `sqfs-intel-DptfDevGen` | 226.7 ms | 226.5 ms | 76,532 -> 76,884 KiB | 0/561 |
| `windows-update-intel-audio-IntcSST` | 396.0 ms | 398.2 ms | 120,076 -> 128,164 KiB | 4/1,672 |
| weighted round | **5,088.1 ms** | **5,091.3 ms** | diagnostic per driver | 49/6,986 |

The largest observed RSS falls from 137,968 to 126,860 KiB. Axeyum-only
weighted time changes by -0.06%, while same-stream Z3 timing varies enough that
the normalized aggregate ratio moves from 0.679x to 0.688x; the absolute
Axeyum result and per-driver RSS are the admission criteria here, not a claim
that a memory ceiling accelerates Z3.

Glaurung `1f24d5d` implements the defaults and reports their identity. A fresh
unset-limit vwififlt smoke selects 9/128, decides and agrees 4,753/4,753 checks,
uses 45 path fallbacks and zero assertion fallbacks/resets, and measures Axeyum
4.477 seconds versus same-stream Z3 4.555 seconds at 129,860 KiB RSS.

## Alternatives

Leaving the opt-in mode unbounded was rejected because ADR-0171's memory cost
was the explicit unresolved admission gate. Four and eight live sessions were
rejected because their cold fallbacks materially erode warm reuse; twelve was
rejected as a no-op on the current tier. A retained-byte estimator would be
more direct than a session count, but it would require new cross-session
accounting and an eviction contract; the existing atomic counter already
delivers a repeatable RSS reduction at unchanged solver time. Automatic warm
selection is rejected until wider held-out drivers validate topology and cost.

## Consequences

GQ7's first memory/capacity gate is complete: explicit lineage reuse now has a
finite, visible, deterministic default envelope and sound one-shot escape. It
remains an opt-in Glaurung integration, not an Axeyum solver default.

Move next to GQ10 widening. Held-out drivers must report assertion/live-path
distributions, fallback rates, Axeyum/Z3 time, and RSS before GQ9 can consider
automatic warm selection. Revisit byte- or AIG/CNF-weighted admission only if
session count ceases to correlate with RSS or the wider tier makes the 9/128
policy regress. GQ8 verdict caching remains unauthorized and would require its
own deterministic capacity, identity, invalidation, and replay decision.
