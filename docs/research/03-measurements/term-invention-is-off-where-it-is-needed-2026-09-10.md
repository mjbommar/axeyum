# Term invention is switched off by exactly the condition that requires it

**Date:** 2026-09-10
**Lane:** coordinator-solver
**Population:** `bench-results/parity-losses-20260908/UF.txt` — the 32 UF files we
return `unknown` on and z3 refutes.
**Depends on:** `does-the-required-instance-enter-our-egraph-2026-09-10.md` (Q2)
and `why-the-instantiation-loop-produces-nothing-2026-09-10.md`.

## The finding

Q2 measured that on **10 of 16 attributable files the term z3 instantiates on is
never built** — and that **66 of the 71 arguments (93%) of those absent terms are
already in our ground set**. We hold the arguments and the Skolem function
symbols; we never form the application.

`qinst_egraph.rs` has the machinery for precisely this. Its doc comment on
`MAX_INVENTED_TERMS_TOTAL` states the case exactly: *"no selection policy can
help; the terms a refutation needs must be BUILT, not found."*

It does not run on the files that need it, and the reason is a gate:

```rust
/// Invention runs only while the accumulated ground set is comfortably below
/// [`MAX_GROUND_TERMS`]: the flood class (fixpoint-free files that drive
/// ground to the cap) must not gain extra term traffic from this route.
const INVENTION_GROUND_CEILING: usize = MAX_GROUND_TERMS / 2;   // 4096
```

Measured with `AXEYUM_QPROBE=1` at a 24 s budget:

| file | max ground | term-invention rounds |
|---|---:|---:|
| f01 | **8192** | **0** |
| f05 | **8192** | **0** |
| f12 | **8192** | **0** |
| f20 | **8192** | **0** |
| f22 | flooded | **0** |
| f29 | 273 | 125 |
| f31 | 2578 | 306 |

The split is total: **zero invention rounds on every flooded file, hundreds on
every file that stays under the ceiling.** Q2 measured that 13 of 18 files reach
the 8192 cap.

## Why this is circular rather than merely conservative

1. The loop admits thousands of junk instances and the ground set passes 4096.
2. Crossing 4096 disables term invention.
3. On these files the required term can only come from invention — it is a
   Skolem-function application no trigger can match, because the application does
   not exist to be matched.
4. So it is never built, and the loop grinds to the 8192 cap on junk.

The gate's stated rationale is sound in isolation — a flooding file should not be
given extra term traffic. But "is flooding" is being used as a proxy for "does not
need invention", and on this population it is the **inverse** of the truth. The
files that flood are the files whose refutation is one application away.

This also explains a result that was otherwise just a shrug: item 3.5 measured an
**8x ground ceiling at zero**, and a 120 s budget at zero. Raising the ceiling
raises the flood with it, so invention stays off and nothing changes. Both arms
were testing capacity against a problem that is a gate.

## What this does NOT explain

**~~f29 is the counterexample, and it is load-bearing.~~ CORRECTED 2026-09-10 by
lane Q6 — see below.** It saturates at 273 ground terms — far under the ceiling —
runs 125 invention rounds, and its required term is *still* absent. I read that
as "on f29 invention ran and formed the wrong application", and treated it as a
second defect distinct from not running at all.

**That is not what happened.** f29 prints its one `egraph-fixpoint` line at
`ground=273`, and Q2's census identifies that block as the **un-Skolemized**
one — which carries no `!qskf_` symbol at all. So all 125 invention rounds ran
where the required term could not possibly be formed, because none of its
ingredients are in scope there. The Skolemized blocks are deadline-bounded and
never enter the invention branch at all.

The error was mine and it is worth naming: I had a per-file aggregate
(`125 rounds`, `ground=273`) and inferred from it that invention had been given a
fair attempt at the target. The probe counts rounds; it does not say **which
assertion set** those rounds ran over, and this file runs several. An aggregate
that does not carry its own scope cannot answer a question about scope.

So f29 is NOT a counterexample to the ceiling story — it is a third case, and
Q6's priming pass moved it into the built column alongside f14, f15, f22 and
f26. The ceiling attribution in the table above stands unchanged; what does not
stand is the claim that category (i) had a second mechanism hiding in f29.

Any fix claiming this item must say which of the two it addresses.

## The falsifiable next step

Raising or removing `INVENTION_GROUND_CEILING` alone is **not** the proposal, and
should be expected to fail: `MAX_INVENTED_TERMS_PER_STEP`'s own comment records
that one 64-term step "blasted the joined-instance admission from 2 to 4098 ground
terms in a single round, drowning the (about nine) refuting instances". Feeding
invention into a set already flooded with junk makes the junk worse.

The observation that would show a real fix worked:

- **f01, f05, f12, f20 report a nonzero `term-invention round` count**, and
- the required Skolem application named in Q2's per-file table is **present** in
  the `AXEYUM_QGROUNDDUMP` output for that file, and
- the 32-file slice decides **more than 1**.

The first two without the third is a mechanism that did not pay. Report all three.

## Outcome, 2026-09-10 (lane Q6): all three were reported, and the third was zero

`building-the-skolem-application-2026-09-10.md` ran exactly this. A bounded
priming pass, placed before the loop where the flood ceiling cannot gate it,
**built the term**: f29's dump gains `(f18 f29 (!qskf_35 !sk_1 !sk_0))`, Q2's
exact missing link, and fully-ground `!qskf_` applications rise on eight of the
ten never-built files (0→229, 0→210, 6→215, …).

The slice still decides **1 of 32**, and the 24-file win list drops to 22, one of
those losses confirmed real on an isolated binary. The pass ships inert at `0`.

So the prediction this section made — that a mechanism firing without moving the
decided count is a failure — was correct, and it fired without moving it. The
construction gap was real, it is closed, and it was not what cost us the
verdicts. The remaining question is downstream of instantiation entirely: why an
e-graph holding the refuting instance's terms, with the instance admitted and
certificate-checked, produces no conflict.
