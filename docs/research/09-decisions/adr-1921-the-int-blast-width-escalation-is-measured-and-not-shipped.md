# ADR-1921: The int-blast width escalation is measured, and not shipped

Status: accepted
Index-summary: The gap log sized QF_NIA's largest single cause as `bounded integer model overflowed at width 32` at **7 of 14** sampled files, and the textbook remedy is an escalating bit-blast width (32 → 64 → 128). Measured over **all 110** winnable files rather than a sample, the width family is **26 of 110 (24 %)**, behind the preprocessed-dispatch timeout (41) and the CNF clause budget (30). An interleaved one-binary A/B — arms alternating per file, `AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH` appending rungs 40/48/56/64 — decides **0 of 110**, with 0 gains, 0 losses, 0 disagreements and +4.6 % wall, and it *destroys the diagnosis*: the 23 precise overflow lines become `Timeout`/`Watchdog`. Nor is it a clock problem: at **150 s** the escalation arm decides 3 of the 23 width-family files and the BASELINE arm at the same 150 s decides *the same three files with the same three verdicts*, so the escalation contributed zero — and **14 of the other 20 report `overflowed at width 64`**, having climbed the whole tail. 128 is unreachable at all (`MAX_INT_BLAST_WIDTH` is 64 and a wider request is a hard `SolverError`, gated by the `i128` model read-back). Decision: **ship the ability to measure it, not the escalation** — the constant ships equal to the existing ladder top so behaviour is byte-identical, with a `cap_lever!` arm, a clamp to what the blaster accepts, and four tests pinning the shipped sequence and the append-only property. Cost to what already works is unmeasurable as the structure predicts (0 losses and wall ratios 0.984 / 0.982 over 41 QF_NIA and 177 cross-division decided files), because the ladder returns on its first replay-checked `Sat`, always below the tail. Soundness: 426 verdicts, 0 disagreements against `:status` (424) and the per-division reference (393), 0 unchecked, checker verified able to fail (817 under a flip control). Standing hypothesis, unmeasured: the blaster constrains **only `int_mul`** against overflow, so the surviving replay failures are ADDITIVE wraparound.
Date: 2026-09-12

## Context

QF_NIA is our worst division: 41/200 against z3's 144 and cvc5's 87, a **+103**
gap. `docs/plan/GAP-LOG-2026-09-12.md` diagnosed half of a 14-file sample as one
cap — `bounded integer model overflowed at width 32`, emitted by `lia.rs:121` /
`combined.rs:223` after the bounded bit-blast finds a model, reads it back as
exact integers, replays it, and finds it false.

The refusal is correct: it is what we do instead of shipping a wrong `sat`. The
standard remedy is an **escalating width** — 32, then 64, then 128 — rather than
a larger constant, because raising `DEFAULT_INT_WIDTH` taxes every integer query
in every division to help a few hard ones.

`DEFAULT_INT_WIDTH` deliberately had no environment lever: lane CAP-LEVERS wired
64 of 74 caps and skipped this one because the width is threaded through ~35
sites and feeds `const INT_BLAST_MAX_WIDTH = DEFAULT_INT_WIDTH`, so a lever would
move the runtime value while the const ladder derived from it stayed put. So the
experiment could not be run without a code change, which is why it had not been.

## Decision

**Ship the ability to measure the escalation; do not ship the escalation.**

Concretely:

- `int_blast_ladder_widths(escalation_top)` in `auto.rs` builds the ladder's
  width sequence, extracted from the solve loop so the sequence is testable
  without a solve.
- `INT_BLAST_ESCALATION_MAX_WIDTH` ships **equal to `INT_BLAST_MAX_WIDTH`**, so
  the escalation tail is empty and the shipped ladder is `[4..16, 24, 32]` —
  byte-for-byte the ladder that shipped before this ADR.
- `AXEYUM_INT_BLAST_ESCALATION_MAX_WIDTH` arms the tail for an A/B without a
  rebuild, and is registered in `config_registry` so it appears in `--trace`'s
  `; config` line.
- The lever is **clamped** to `axeyum_rewrite::MAX_INT_BLAST_WIDTH` by the ladder,
  never passed through to the blaster.

`DEFAULT_INT_WIDTH` itself is **not** made runtime. The escalation does not need
it: the ladder top is a separate private constant, and the ~35 direct call sites
that blast at `DEFAULT_INT_WIDTH` are unaffected by a longer ladder. The
concern the CAP-LEVERS lane recorded — a lever that moves the runtime value while
the derived const ladder stays put — is avoided by levering the ladder, not the
width.

## Evidence

Full measurement:
[`qf-nia-is-not-a-width-problem-2026-09-12.md`](../03-measurements/qf-nia-is-not-a-width-problem-2026-09-12.md).
Per-file data: `bench-results/qf-nia-width-20260912/`.

**The width is 21% of the gap, not 50%.** Census of **all 110** winnable QF_NIA
files (not a sample): timeout 41, CNF clause budget 30, **width overflow 23**,
watchdog 12, out-of-range constant 2, `distinct` limit 1, in-range `unsat` 1. The
whole width family is 26 of 110.

**Escalation to 64 decides zero.** Interleaved A/B, arms alternating per file,
one binary, 220 solves: baseline 0 decided, escalation 0 decided, 0 gains, 0
losses, 0 disagreements, +4.6% wall. It also destroys the diagnosis — the 23
precise overflow lines become `Timeout`/`Watchdog`.

**Not a budget problem either.** The 23 width-family files at **150 s**: the
escalation arm decides 3, and the baseline arm at the same 150 s decides *the
same three files with the same three verdicts*. The escalation contributed zero
of them. 14 of the remaining 20 report `overflowed at width 64` — they climbed
the entire tail and failed replay at the top rung.

**The cost to what already works is unmeasurable**, as the structure predicts:
41 QF_NIA decided files and 177 decided files across QF_LIA/UFLIA/IDL/NRA/ABV,
0 losses, 0 disagreements, wall ratios 0.984 and 0.982 on the both-decided sets.
The ladder returns on its first replay-checked `Sat`, which is always at a width
at or below the historical single width, so a decided query never builds a tail
rung.

**Soundness.** 426 verdicts, cross-checked by full path against the benchmark's
own `:status` (424 comparisons) and the per-division reference solver (393):
**0 disagreements, 0 unchecked**. The checker was verified able to fail —
flipping every verdict yields 817.

## Alternatives

- **Raise `DEFAULT_INT_WIDTH` to 64.** Rejected without a separate sweep: the
  escalating ladder is a strict superset of what a raised constant reaches on
  these files (it tries 64 *and* everything below), and it decides none of them.
  A raised constant cannot decide a file that the ladder including width 64 does
  not, so its only distinct effect here would be the cost on every other integer
  query — a cost with nothing on the other side.
- **Escalate to 128.** Not reachable. `MAX_INT_BLAST_WIDTH` is 64 and
  `blast_integers` answers a wider request with `InvalidWidth`, a hard
  `SolverError`, not an `unknown`. The ceiling is the `i128` model read-back, so
  128 means a bigint read-back through the whole projection path.
- **Delete the lever and the constant.** Rejected: the measurement is about *this*
  population at *this* budget, and the next lane with a different population
  should be able to re-run it with one environment variable rather than
  rediscovering the refactor.

## Consequences

- QF_NIA's width class is **closed as a lead**: 23 of 110 files, none of them
  winnable by widening within what the blaster accepts.
- The two classes that are actually larger are the **preprocessed dispatch
  timeout** (41) and the **CNF clause budget** (30). The latter already has a
  measured negative (lifting it by the estimator's own 9.4x slack decides 0 of
  49, `docs/plan/notes/118-nia-diagnosis.md`), so the timeout class is where a
  QF_NIA lane should start.
- One new hypothesis, stated as a hypothesis: the blaster constrains **`int_mul`**
  against overflow and nothing else, so the replay failures that survive are
  additive wraparound. An additive no-overflow constraint is sound by the same
  argument as the multiplicative one. Unmeasured.
- Revisit if the blaster's `i128` read-back is ever replaced, or if a different
  division's census puts the width class above the timeout class.
