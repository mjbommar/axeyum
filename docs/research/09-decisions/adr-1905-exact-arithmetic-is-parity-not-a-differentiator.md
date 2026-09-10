# ADR-1905: Exact arithmetic is parity with Z3, not a differentiator — the row is removed, and the sweep says it was the only place the claim survived

Status: accepted
Index-summary: Z3's `lp::mpq` is its bignum `rational` and its simplex values are rational+δ, the same as ours, so exactness is a tie and stops being listed as ours. One row removed from `02-z3.md`'s "We have, they do not" table, one correction marked done in `10-gap-analysis.md`. The sweep behind that: roadmap 4.5 was framed as "remove from any comparison prose", implying several sites — a two-token search over every `.md` and `.rs` in the tree, with a positive control, finds the claim surviving in exactly ONE place. Recording the denominator, because "we corrected it in six places" and "there was one place" are different states of the world and only one of them is true.
Date: 2026-09-10

## Context

Roadmap item 4.5 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md:111`](../../solver-comparison-2026-09/11-roadmap-and-plan.md):

> **Stop claiming exact arithmetic as a differentiator.** Z3's `lp::mpq` is
> bignum rational + δ, same as ours. | Remove from any comparison prose.

The technical premise is right and was measured first-hand by the Z3 review:
`02-z3.md:649` reads `src/math/lp/numeric_pair.h:34, :297` and reports that
`lp::mpq` is a `typedef` of Z3's bignum `rational`, that simplex values are
`impq = numeric_pair<mpq>` — a rational plus an infinitesimal δ coefficient with
lexicographic ordering — that model extraction is `v.x + δ·v.y`
(`lar_solver.cpp:509`), and that the only `double` in Z3's arithmetic path is
heuristic pivot scoring (`numeric_pair.h:287`). The legacy `theory_arith` is
equally exact; its fixed-width `s_integer` variants are commented out.

Our side is exact too, and measured: zero `f64`/`f32` across all eleven
`nia_*`/`nra_*` files and all of `axeyum-arith`, with a positive control
(`04-arithmetic-theories.md`). Both measurements are good. **They establish
parity, and parity is not a differentiator.**

The instruction "remove from any comparison prose" carries an implicit claim of
its own — that the assertion is *scattered*. That claim needed checking before
acting on it, because "the ADR says stop claiming X while the tree still claims
X in six places" and "the ADR says stop claiming X and there was one place" are
different outcomes, and only a sweep distinguishes them.

## Decision

**Exact arithmetic is recorded as parity with Z3 and is removed from the
"we have, they do not" framing. Both measurements are kept; only the
classification changes. The sweep behind the removal is recorded, including its
method, its positive control and the fact that it found ONE site — because the
denominator is part of the finding.**

Three commitments.

### 1. The classification, stated once so it is not relitigated

Exactness is a **tie**. Not a small lead, not a lead we have stopped
advertising: a measured tie, on both sides, with sources cited on both sides.
Anyone re-adding it to a differentiator table needs a new measurement showing
Z3's arithmetic is inexact somewhere it matters, and `numeric_pair.h:287` says
where to look first — the heuristic pivot scoring is the only `double`, and
heuristic scoring cannot make a verdict unsound.

### 2. What was changed

| file | change |
|---|---|
| `docs/solver-comparison-2026-09/02-z3.md` | **Row removed** from the table headed "### 2. We have, they do not": *"Exact arithmetic everywhere on the verdict path, measured"*. Its closing paragraph now names the removal, keeps both measurements as a parity statement, and names the general form of the mistake. |
| `docs/solver-comparison-2026-09/10-gap-analysis.md` | The bullet under "Corrections to claims we have been making" said *"We should stop listing this as an advantage"* — an instruction. Now marked **done**, pointing here. |

Nothing else in the tree required a change, per §3.

### 3. The sweep, its method, and its denominator

**Method.** Over every `.md` and `.rs` in the tree (excluding `.git`), take the
intersection of two token classes:

```sh
grep -rniE 'exactness|exact[- ]rational|exact[- ]arithmetic|exact[- ]simplex|exact[- ]number' \
     --include=*.md --include=*.rs . \
  | grep -v '^\./\.git' \
  | grep -iE 'z3|cvc5|bitwuzla|boolector|yices|mathsat|opensmt|smtinterpol|stp|differentiat|advantage|unlike|uniquely|nobody else|no one else|other solvers|reference solver|ahead of|better than|only solver'
```

An exactness token AND a comparison-or-advantage token on the same line. This is
deliberately over-broad: it is meant to over-report and be triaged, because an
empty grep is not a negative result.

**Positive control.** The command finds `02-z3.md:1399` and
`10-gap-analysis.md:124` — the two sites already known to make or correct the
claim. A search that could not find the thing it is looking for would have
returned nothing here, and the run would have proved only that the pipeline was
broken.

**Result, by file, before triage:**

| file | lines | verdict |
|---|---|---|
| `docs/foundational-resources/generated/*.md` (4 files) | 83 | false positives — `stp` matches inside unrelated words in generated curriculum dashboards; the rows say "LRA (exact rationals)" about our own math artifacts, no comparison |
| `docs/solver-comparison-2026-09/02-z3.md` | 5 | **1 real** (`:1399`, the row). `:649` describes Z3 neutrally; `:1289` describes a route; two are incidental |
| `docs/solver-comparison-2026-09/10-gap-analysis.md` | 1 | the existing correction, not a claim |
| `docs/solver-comparison-2026-09/{00-README,04-…,05-…}.md` | 3 | neutral descriptions ("exact simplex and interpolation, two things we built and cannot currently evaluate"; Yices's stock configuration; a scope row explicitly labelled *"not a win on their home ground"*) |
| `docs/solver-comparison-2026-09/11-roadmap-and-plan.md` | 2 | items 4.1 and 4.5 themselves |
| `docs/research/09-decisions/adr-1813-…md` | 1 | describes Z3's `theory_lra` route |
| `docs/research/09-decisions/adr-0301-…md` | 1 | about the CAS initiative, not a solver comparison; ADRs are immutable in any case |
| `docs/research/08-planning/capability-matrix.md` | 1 | a QF_NRA row; "exact rational arithmetic" describes a certificate checker |
| `docs/research/02-ecosystems/…/cvc5.md` | 1 | describes cvc5's `replayLog` |
| `docs/research/10-cas/diary.md` | 4 | CAS entries, no solver comparison |
| `docs/plan/track-2-theories/P2.4-lia-cuts.md` | 1 | "axeyum's existing exact-rational simplex, adding Z3's cut portfolio" — a plan, not a claim of advantage |
| `crates/axeyum-solver/src/config_registry.rs` | 1 | a memory-accounting note |

**Denominator: one.** The claim survived in exactly one place, and that place
already carried its own correction inline. Two secondary searches agree:
`grep -rniE 'differentiator|sets us apart|our .* advantage|uniquely ours'`
returns 30 hits across the tree and **not one** ties exactness to the
differentiator — they are all about trusted checking, proofs, counterexamples or
models. And `grep -rniE '(unlike|whereas|z3 uses|other solvers).{0,120}(exact|rational|float|double)'`
returns one relevant hit,
[ADR-0015](adr-0015-linear-real-arithmetic.md)`:52` — "rationals keep it sound
and the model checkable, unlike floating point" — which is a *technique*
rationale (exact versus floating-point simplex is a real design choice), not a
claim about Z3, and is in an immutable accepted ADR regardless.

## Evidence

- `docs/solver-comparison-2026-09/02-z3.md:649` — the first-hand Z3 read
  (`numeric_pair.h:34, :297`, `lar_solver.cpp:509`, `theory_arith.h:1171-1275`).
- The removed row's own text, which already said "**this row is a tie**, and we
  should stop claiming it as a differentiator" — the review that measured Z3
  caught its own error and annotated it; this ADR finishes the job by removing
  the row rather than leaving a table whose contents contradict its heading.
- The sweep above, with its positive control, its full per-file result, and its
  two corroborating searches.
- **Nothing in this ADR was re-derived from Z3 source.** `references/z3` is
  absent (`ls references/` → `README.md` only), so the `lp::mpq` reading is
  inherited from `02-z3.md`, which took it first-hand. Said plainly because this
  ADR's whole subject is a claim about someone else's code that was believed
  without checking their half.

## Alternatives

- **Leave the row in place with its inline caveat.** Rejected. A table headed
  "We have, they do not" containing a row that says "this is a tie" is a
  self-contradicting artifact, and the caveat is the part a skim drops. A reader
  counting rows in that table gets the wrong number.
- **Delete both measurements along with the row.** Rejected. Zero `f64`/`f32`
  across our arithmetic path, with a positive control, is a real and useful
  property — it just is not *distinguishing*. Deleting a measurement because its
  conclusion changed is how a document loses the ability to be checked.
- **Restate the row as "exactness with a Farkas certificate", which IS ours.**
  Rejected as a re-run of the same error one level up. The differentiating half
  is the *certificate*, and it already has its own row ("Farkas certificates on
  the default LRA path"). Merging exactness into it would smuggle the tie back
  in behind something true.
- **Search only `docs/solver-comparison-2026-09/`, where comparison prose
  lives.** Rejected: that assumes the answer. The claim could have propagated to
  `README.md`, `STATUS.md`, `PARITY.md`, capability text in `support_matrix.rs`,
  or a crate doc comment. Checking cost one command; assuming would have cost
  the finding in §3.
- **Assume the roadmap's implied "several places" and hunt until six are
  found.** Rejected, and worth naming as the trap: a brief that says "remove it
  from the six places" plus a searcher determined to find six is how neutral
  descriptions get edited into corrections and a document loses accuracy in the
  name of gaining it. The instruction was a hypothesis; the sweep tested it.

## Consequences

**What this buys.** One fewer overstatement in the document we hand people who
ask how we compare to Z3, and a measured denominator so nobody re-runs this
sweep. The general failure mode is written down where the mistake was made
(`02-z3.md`): *we measured our own side carefully, did not measure theirs, and
filed the result under "we have, they do not".* That is a reusable check for
every remaining row in that table.

**What is LOST by deciding this way.**

- **The "We have, they do not" table is one row shorter**, and it was a row that
  read well. Anything that made the table longer felt like a win; the honest
  version is shorter. Expect this to recur — the same audit applied to the other
  rows may shorten it further, and nobody has run it.
- **The remaining rows are not re-verified by this ADR.** They were measured by
  the Z3 review and are not re-checked here. The exactness row was caught by the
  reviewer who wrote it, which is the good case; a row whose Z3 half was *not*
  measured would look exactly like a row whose Z3 half was measured and came out
  in our favour. This ADR removes one such row and does not establish that there
  are no others.
- **A referee could reasonably ask why this needed an ADR at all**, since one
  row was deleted and one bullet updated. The answer is the denominator: without
  §3 written down, the next reader of roadmap 4.5 has to redo the sweep to learn
  that "remove from any comparison prose" was already almost entirely done.

## What would falsify this decision

1. **A measurement showing Z3's arithmetic is inexact on a path that decides a
   verdict.** `numeric_pair.h:287` is the only `double` and it is pivot
   heuristics; if a verdict-bearing `double` is found, exactness becomes a real
   differentiator again and the row should return with that citation.
2. **The sweep in §3 missing a site.** It is two token classes intersected; a
   claim phrased without any of those tokens — "we never round", "bignum
   throughout", "no approximation anywhere" — would slip past it. Anyone who
   finds such a site should add its phrasing to the token list rather than just
   fixing the line.
3. **A comparison against a solver that is genuinely inexact.** The claim is
   dead against Z3 and cvc5. If a future parity table includes a solver using
   floating-point arithmetic in its simplex, exactness is a differentiator
   *there*, and the honest form names the opponent rather than claiming it in
   general.
