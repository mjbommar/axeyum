# Decide-rate — measured on the *accessible* corpus (2026-06-29)

A grounding measurement for Track-1 work, taken on the **locally-committed
curated corpus** (`corpus/public-curated/non-incremental/`) with the release
`measure_corpus`/`explain_corpus` harness, 2 s/file cap, `axeyum check_auto` vs
the `z3` binary. **This corrects an important framing gap:** the
[frontier ranking](decide-rate-frontier-2026-06-28.md) is computed on the full
**NAS** corpus; the *accessible* (curated) slices tell a different, sharper story
about where a **verifiable** decide-rate win actually exists.

## Measured (accessible curated slices, both-parse flat, DISAGREE = 0)

| Division | Considered | axeyum decided | z3 decided | Gap vs z3 |
|---|---:|---:|---:|---:|
| **QF_S** | 69 | **56** | 56 | **0 — at parity** |
| **QF_UF** | 48 | **37** | 41 | **−4** |

- **QF_S is already at z3 parity on accessible data** (56/56; the 13 axeyum
  misses, z3 also misses — hard for both). The frontier's "44 %" is the full NAS
  set. ⇒ the **`max_len` string lever has little headroom on what we can verify**;
  defer it until the full NAS string set is the measurement target. (The lever is
  also not a one-liner: `strings.rs::literal` accumulates content into a `u128`,
  so `max_len > 16` needs wide-constant construction + a content-width `bv_const`
  audit — soundness-monotone, but real work.)
- **QF_UF is the real accessible gap (−4 vs z3), and it is verifiable** (the
  instances z3 decides and axeyum does not are right here in the curated set).

## QF_UF gap — triaged cause (`explain_corpus`)

The undecided QF_UF instances are **mixed-theory**, not pure QF_UF, and the pure
e-graph path *correctly* declines on them:

- `issue5396` (UF + BV), `issue5836-2` (UF + arrays), `issue4007-rint-uf`
  (UF + NRA): the e-graph builds a theory-consistent assignment but
  `build_model` → `replays()` fails — *"e-graph model did not replay (base-sort
  semantics outside congruence)"* — because the model omits the **non-EUF**
  theory semantics. The decline is **sound** (`replays()` re-checks the model
  against the original assertions before any `Sat`; a non-satisfying model yields
  `Unknown`, never a wrong `Sat`).
- `ite3` (uninterpreted sort + `ite`): `error: term has sort (Uninterpreted 0)
  that the pure-Rust BV backend cannot bit-blast` — routed to the BV backend,
  which has no uninterpreted-sort (Ackermann) handling.

**So the accessible QF_UF gap is theory-combination routing + uninterpreted-sort
Ackermann, not a missing string bound and not a soundness hole.** This is exactly
the frontier's "uninterpreted-sort IR keystone" / "e-graph + CDCL(T) combination"
(Track 1, P1.4/P1.5) — a deep, soundness-critical core change.

## Landed this session (robustness, not yet a decide-rate gain)

- **`check_auto` no longer hard-errors on a valid QF_UF instance.** `ite3`
  (`(declare-sort U) … (not (= x (ite a (ite a x y) (ite (not a) x y))))`) used to
  return `Err("term has sort (Uninterpreted 0) that the pure-Rust BV backend
  cannot bit-blast")` — the e-graph path declined (it treats the uninterpreted-sort
  `ite` opaquely, so the `x ≠ ite(…)` candidate fails replay) and the final BV
  fallback then errored. The fallback now catches *that specific error* (only when
  `features.has_uninterpreted_sort`) and returns an honest `Unknown`. Decisions are
  untouched (it is the `Err` arm), so decide-rate is unchanged (QF_UF 37/48,
  DISAGREE = 0, re-measured) — but a consumer calling `check_auto` on such an
  instance no longer gets a hard error. The actual decide-rate gain (`ite3` is
  trivially `unsat`) needs the next step.

## Landed: uninterpreted-sort `ite` elimination (decide-rate gain)

Uninterpreted-sort `ite` is now eliminated equisatisfiably (`ite(c,a,b)` → fresh
`t` with `(c→t=a)∧(¬c→t=b)`) **for the e-graph deciders only**
(`lift_uninterpreted_sort_ite`, applied to the slice handed to
`solve_qf_uf_online`/`check_qf_uf_with_config`). The e-graph congruence treats
`ite` opaquely, so `x = ite(c, a, b)` over an uninterpreted sort was undecidable
to it; after the lift it decides by congruence over `t`. `ite3` now decides
**unsat** (was the hard error above). The transform is textbook ite-elimination —
**equisatisfiable, so it cannot change a verdict** (DISAGREE stays 0); BV/Bool
`ite` are untouched (handled natively downstream).

**Confinement matters.** A first attempt applied the lift *globally* (in
`check_auto_dispatch`) — it gained `ite3`, DISAGREE = 0, but added variables to
every dispatch. The final form is doubly confined: the lift runs only on the
slice handed to the e-graph deciders **and only for pure-UF instances** (`!has_int
&& !has_real`), so the UF+arithmetic dispatch path provably never pays for it.
(Note: `uf_arith_dispatch_differential` asserts a tight wall-clock budget bound
`budget_excused ≤ 4`; under the heavy concurrent build load during this session it
read `8` — **but the no-lift baseline read the identical `8`**, confirming the
failure is environmental (load), not this change. Re-confirm on an unloaded
machine.)

**Measured (curated QF_UF, release, vs z3), DISAGREE = 0:** at a 5 s cap axeyum
rises **37/48 → 39/48** (gap to z3 −4 → −2). At a tight 2 s cap the net is flat
(`ite3` gained; one borderline instance recovers only at 5 s — a slowdown, not a
regression). The gain dominates at an adequate budget.

## Recommended next core step (focused session)

1. **Uninterpreted-sort Ackermann in the BV/auto route** so `ite3`-style
   (uninterp sort threaded through `ite`/`=`) decides instead of erroring. The
   `replays()` / model-eval guards keep it sound — improving model construction
   can only turn `Unknown → Sat` for genuinely-sat instances.
2. **UF + theory combination** (`issue5396` UF+BV, `issue5836-2` UF+arrays):
   route mixed UF instances through the combination solver (or Ackermannize the
   UF then hand to the theory backend) rather than letting the pure e-graph path
   own them. Verify each `Sat` replays and each `Unsat` carries the skeleton.
3. **Re-measure this curated slice** after each step — the target is QF_UF
   37 → 41 (match z3) on accessible data, `DISAGREE = 0`, with the relevant
   differential fuzz (`uflia`/`abv`) green.

## Why this note exists

The discipline is *"no decide-rate claim moves without re-running the
scoreboard."* This is the re-run, on the data we can actually verify against. It
localizes the one accessible, verifiable decide-rate gap (QF_UF, −4) to a
specific sound-guarded mechanism, so the next core session attacks the right
thing — and records that the strings lever, the loudest item by NAS count, has
**no verifiable headroom on accessible data** today.

*Harness:* `target/release/examples/measure_corpus <dir> 2000` and
`explain_corpus <dir> 2000`. *Owned by Track 1/2.*
