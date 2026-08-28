# The `creal_prelude_builds` band is itself a regression, normalized

Date: 2026-08-28. Found by a lane sent to investigate a *different*, and
imaginary, regression.

## What happened

I reported `int_prelude` at 8.65 s before a merge and 148 s after, and
dispatched a lane to find the cause. It found three things, in ascending order
of importance.

**1. My measurement was wrong, and the mechanism is worth knowing.**
`int_prelude` is a **substring** filter, and
`creal_point::creal_point_tests::cpoint_prelude_builds` matches it —
`cpo` + `int_prelude` + `_builds`. That one test was 148.55 s of the 150 s run.
My "before" used `int_prelude::` (with colons, 34 tests) and my "after" used
the bare form (38 tests, including the `creal_point` one). **The two numbers
never measured the same set.** The only visible tell is the test count.

**2. The change I suspected costs +0.29 s.** Filtering with the colons: parent
34 tests / 3.82 s → HEAD 37 tests / 4.11 s. The three new Bézout evaluation
tests are 0.136 s, 0.070 s and 0.179 s. The largest `Nat` formed anywhere in
them is **6**, so the unary-numeral mechanism never engages — that hypothesis
is refuted, not merely unsupported.

**3. `creal_prelude_builds` went 12.19 s → 108.40 s in two days.** 8.9x.

## Why nobody noticed: the band

Every `creal` lane today measured `creal_prelude_builds` at 95–120 s and
reported "in band, no regression". I did too, repeatedly. The band is
**94–123 s**.

That band appears **only in lane status files** (`176-cw-bridge.md`,
`177-inline-hunt.md`, `180-pi-r2d.md`, `181-pi-r2e.md`). It is not pinned in
`CLAUDE.md`, not enforced by a gate, and not derived from anything. It is a
norm that lanes established **by observing each other**, during a window in
which the prelude was already ~8x its documented cost.

`CLAUDE.md` records the true figure without anyone connecting it: one
declaration took the build **18.7 s → 92.6 s**, was diagnosed, and was
**"Restored to 18.4 s"** on 2026-08-26. A lane measured **12.19 s** at a commit
from that same day. So the prelude built in 12–18 s two days ago and builds in
108 s now, and the band ratified the difference as normal.

This is a measurement failure of a specific kind: **a threshold inferred from
recent observations cannot detect a drift that was already underway when the
observations began.** It is self-confirming. Each lane's "in band" reading was
honest and locally correct, and the aggregate was wrong.

## What is NOT claimed

- Not that any particular lane caused it. **378 commits touched `creal.rs` or
  `creal/` since 2026-08-26**; the growth is plausibly cumulative and ordinary.
- Not that 12.19 s is achievable now. The prelude has genuinely gained
  content — EVT row 2 and its gap closure, supOn rungs 1–6, pi rungs 2–3, the
  integral family. Some growth is real work.
- Not that the `CReal.integral` mechanism `CLAUDE.md` documents is the cause
  again. That is the *known* way to lose an order of magnitude here, which
  makes it the first thing to check and not the conclusion.

## What to do

1. **Bisect `creal_prelude_builds` across the 378 commits.** The technique that
   worked before is in `CLAUDE.md`: when one declaration dominates, bisect
   WITHIN it by legs. Measure with the prebuilt binary under
   `target/debug/deps/` — it takes no cargo lock, so it measures the work
   rather than the flock queue.
2. **Replace the band with a pin that can go red.** A number nobody wrote down
   deliberately cannot detect drift. `artifacts/kernel-stack-envelope.tsv` is
   the model: a measured value, in a file, with a gate that re-demonstrates it
   can fail.
3. **Distinguish "grew because it does more" from "grew because a term
   unfolds".** Only the second is a defect, and the two are indistinguishable
   from the wall clock alone.

## The general lesson

**A tolerance band derived from recent runs measures your recent runs, not
correctness.** This one was quoted in four status files, enforced in a dozen
briefs including several of mine, and cited by lanes as evidence their work was
clean. It was never anything but the average of an ongoing regression.
