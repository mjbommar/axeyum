# Lane: round-cap — two populations, one boundary, and a round cap that is a loss at every value

<!-- plan-section: lane-status -->

**Lane round-cap (`DONE`, round-cap, 2026-09-14).** The split was asked for
before anything was built; it was done first, and it decided the rest. Full
reasoning in [ADR-2035]; artifacts in
[`bench-results/round-cap-20260914/`](../../../bench-results/round-cap-20260914/PREREGISTRATION.md).

Branch base: `git merge-base main HEAD` is
`ffaf920cd585300b5c3c854f88db9d8ee8517759`, which **is** local `main`'s HEAD.

## 1. The split is mechanical, not a threshold — 12 BORN-OVER / 10 GROWN

| | test | n |
|---|---|---:|
| **GROWN** | `sat_candidates >= 1` — a round was **admitted** past the boundary and returned a model, so the refusal is on a LATER round over a skeleton the batch grew | **10** |
| **BORN-OVER** | `sat_candidates == 0`, `solve_rounds == 1`, `lemmas_added == 0` — the **first** solve was refused, before a single lemma existed | **12** |
| UNCLASSIFIED | — | **0** |

22 files, one observation each, no residue. It agrees exactly with [ADR-2030]'s
`lemmas_added >= 100` threshold, with nothing in between — so the threshold was
not wrong, it was unjustified, and now it is not.

**On the 12 BORN-OVER files no cap of any kind can help**, because the refusal
precedes the first lemma.

## 2. The round cap is a LOSS at every value

`check_with_function_consistency` has three exits, and truncation can only
produce `Unknown`. On BORN-OVER the refusal is at round 1; on GROWN round 1
returned a functionally *inconsistent* model (`violated_pairs >= 8` on all ten).
**Upside zero, structurally.**

The downside was invisible to the census, because `FunctionConsistencyStats`
reaches the outside world only through `wrap_unknown` — a query the CEGAR
*decides* leaves no round count behind. With a probe at all three exits, over
the whole 129-file population:

| | census | measured |
|---|---|---|
| `solve_rounds` range | 1–3 | **1–27** |

| cap | deciding loops truncated | files that lose a decision |
|---:|---:|---:|
| 1 | 324 | **61** |
| 2 | 114 | **38** |
| 3 | 87 | **27** |
| 4 | 28 | **16** |

The non-run was pre-registered before measuring.

## 3. The boundary: calibrated six days ago, for a job it is not doing

Two commits ever touch it; the current value is from `832c2afd0` (2026-09-08),
re-derived against the engine that actually runs. **Not the `64` case.** But its
origin (`8a6de50ac`, 2026-08-10) is a rectangle *fitted* to readmit one file
while two named abort controls kept declining, and its memory story is refuted
by its own re-derivation (71 MiB peak against an 8 GiB ceiling; the control it
names does not reach the gate). *"Above this nobody has measured"* is no longer
true — [ADR-2020] measured 0 of 129 at 4x. **Correct as set; do not raise it.**

## 4. The lever that was measured, and the wiring that IS missing

[ADR-2020] §8.3's **second** missing wiring, untested by [ADR-2030]: the
`oversized_admission_probe` rescue is wired only into `check_with_arith_dpll`.
An ordered probe over all 129 files on the shipped path:

| | OFF |
|---|---:|
| files crossing the boundary | **47** |
| ...only at `site=solve` (**no** rescue) | 35 |
| ...only at `site=preflight` (rescue shipped) | 12 |
| ...at **both** | **0** |

**0 of 47 cross both**, so the gap is real — the opposite of the first missing
wiring. **And closing it is worth zero:** with the rescue on it **ran on 36
files and decided on 0** (`declined` 36 of 36). A/B: **0 gains** on 129, on the
22 targets, and on the 35 files where the lever actually runs. Ships OFF.

## 5. Two guards of mine could not fail, and the mutations found both

The first polarity fixture was `x <= 0`, which the rescue refuses at its own
difference-logic gate — so it returned `None` in both arms for a reason
unrelated to the lever, and inverting the polarity killed **0 of 1757**. Fixed
to a non-DL query with a companion control asserting the rescue *does* decide
it. Separately, the one-shot test consumes the process's only rescue attempt and
would have disarmed the polarity test by running first. Three guards now, each
mutation-verified at **exactly one** test killed.

## 6. What is still open

[ADR-2020]'s redirect survives everything here: the reference refutes 21 of
these 22 files at a median 70 ms, nine without instantiating a quantifier. The
target is the SIZE of the ground set, and **selection** is the axis. Ten
explanations are closed and none of them is selection.
