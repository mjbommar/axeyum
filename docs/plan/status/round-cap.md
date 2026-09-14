# Lane: round-cap — two populations, one boundary, and the rescue that is wired to the wrong site

<!-- plan-section: lane-status -->

**Lane round-cap (`WIP`, round-cap, 2026-09-14).** Splitting [ADR-2030]'s two
populations before building anything, per the brief. Artifacts in
[`bench-results/round-cap-20260914/`](../../../bench-results/round-cap-20260914/split-populations.txt).

Branch base: `git merge-base main HEAD` is
`ffaf920cd585300b5c3c854f88db9d8ee8517759`, which **is** local `main`'s HEAD.

## 1. The split is mechanical, not a threshold — 12 BORN-OVER / 10 GROWN

[ADR-2030] split by `lemmas_added >= 100` and reported 10 flooded / 12
unflooded. A threshold cannot distinguish *"the flood pushed this over the
boundary"* from *"this was already over and happens to have emitted lemmas"*.
The CEGAR loop's own statistics make the split structural:

| | test | n |
|---|---|---:|
| **GROWN** | `sat_candidates >= 1` — some round's solve was **admitted** past the boundary and returned a model, so the refusal is on a LATER round over a skeleton the lemma batch grew | **10** |
| **BORN-OVER** | `sat_candidates == 0`, `solve_rounds == 1`, `lemmas_added == 0` — the **first** solve was refused; the instantiated conjunction crossed the boundary before a single lemma existed | **12** |
| UNCLASSIFIED | — | 0 |

One observation per file, 22 files, no residue. It **agrees exactly** with
[ADR-2030]'s threshold — every `lemmas_added >= 100` is GROWN and every
`lemmas_added == 0` is BORN-OVER, with nothing in between — but now for a
reason rather than a cut point.

**The consequence the brief asked not to lose:** on the 12 BORN-OVER files no
lemma cap and no round cap can do anything at all, because the refusal precedes
the first lemma. That is 12 of the 22, and 12 of [ADR-2020]'s largest bucket.

## 2. The census label covers two code sites, and all 22 are at one of them

`pre-SAT skeleton exceeds the joint resource boundary` is emitted by
`pre_sat_skeleton_boundary_reason`, which is called from **two** places with
different rescue wiring. The reason carries a `stage` suffix that separates
them, so the split is readable from the committed census:

| stage | site | rescue available | n |
|---|---|---|---:|
| `declining before the online CDCL(T) probe` | `arith_dpll_admission_preflight` (`dpll_lia.rs:1518`) | **yes** — `oversized_admission_probe` runs first | **0** |
| `declining before the first SAT round` | `IncrementalArithDpll::solve` (`dpll_lia.rs:1158`) | **none** | **22** |

Zero of the 22 carry `reusable_arith_lemmas=`, so they did not arrive through
`check_with_arith_dpll_reusing_lemmas` either. The route is
`check_with_uf_arithmetic_lazy` → `check_with_function_consistency` →
`check_with_incremental_arith` → `IncrementalArithDpll::solve`, which reaches
the boundary directly and returns.

This is [ADR-2020] §8.3's *second* missing wiring — the one [ADR-2030] did not
test. **It is still a census claim about the last site to refuse, so it is being
verified with an ordered probe before anything is built on it.**

## 3. Next

Ordered probe, then a lever if the probe supports one, then the A/B with a
loss-detecting control and a noise floor.
