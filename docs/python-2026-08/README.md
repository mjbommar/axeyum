# Python layer and agentic frontier — August 2026

> **This is the automation strand.** It sits beside the three existing strands
> — [`refactor-2026-08/`](../refactor-2026-08/README.md) (engineering floor),
> [`mathematics-2026-08/`](../mathematics-2026-08/README.md) (mathematical
> ceiling), [`formalized-math-2026-08/`](../formalized-math-2026-08/README.md)
> (collecting formalized mathematics) — and beside the long-horizon
> [Autogenesis programme](../autogenesis/README.md). It asks one question:
> **how does a script, a notebook, or an autonomous agent drive the Rust
> engines and read the knowledge artifacts without gaining any authority the
> Rust API lacks?**

Three plans, in dependency order. Each is bounded, has exit criteria that a
command can check, and lands as slices that pass the gates on their own.

| # | plan | what it delivers | depends on |
|---|---|---|---|
| 01 | [`01-pyo3-maturin.md`](01-pyo3-maturin.md) | `crates/axeyum-py` + root `pyproject.toml` + `python/axeyum/` package + stub generation + `just py-check` gate | nothing |
| 02 | [`02-python-api.md`](02-python-api.md) | the typed surface: `axeyum.smt`, `axeyum.solver`, `axeyum.ir`, `axeyum.cas`, `axeyum.kernel`, `axeyum.producers`, `axeyum.knowledge`, `axeyum.evidence` | 01 |
| 03 | [`03-agentic-layer.md`](03-agentic-layer.md) | pydantic-ai agent over 02, replayable episode artifacts, fail-closed episode checker, the frontier loop | 01, 02 |
| 04 | [`04-tactic-catalog.md`](04-tactic-catalog.md) | the proof-strategy vocabulary `Plan` resolves against; census rule that rejects a one-shape catalog | 03 |
| 05 | [`05-agent-runbook.md`](05-agent-runbook.md) | install, run offline/live, replay, where episodes go, what the checker enforces | 03 |
| 06 | [`06-obstruction-graph.md`](06-obstruction-graph.md) | typed declines to an obstruction graph; which capability removes the largest cluster | 03 |
| 07 | [`07-mobility-census.md`](07-mobility-census.md) | every precondition against every open fact without running a producer; the capability backlog | 03, 04 |
| 08 | [`08-guarded-tools.md`](08-guarded-tools.md) | the two guarded tier-R tools: the `web_fetch` prefix allowlist, the nursery family rule, the injection fence, and the sandbox that must be shown to bite | 03 |
| 09 | [`09-coverage-plan.md`](09-coverage-plan.md) | the generated coverage ledger (`scripts/gen-python-coverage.py`) that evaluates 02's exit criterion, and the slice plan for the gaps it measures | 02 |
| 10 | [`10-quality-best-practices.md`](10-quality-best-practices.md) | current PyO3/maturin practice (sourced) against the measured binding; six quality slices Q1–Q6 | 01, 02 |
| 13 | [`13-panic-surface.md`](13-panic-surface.md) | the measured panic surface a Python caller can reach (`panics=3` -> `0`), the preflight-vs-`catch_unwind` rule, and the panics that are unreachable by construction | 01, 10 |
| 14 | [`14-frontier-reachability.md`](14-frontier-reachability.md) | why the agent attempted ~3 of 146 open facts, decomposed into reachability (frozen-export coverage, `gen-statement-adapters.py`) × provability (producer reach), plus the 2026-08-26 correction that the observed lean4export arrow cap was an output/storage artifact | 03 |
| 12 | [`12-wheels-and-release.md`](12-wheels-and-release.md) | the release-wheel matrix (abi3 + a version-specific 3.14t wheel + sdist), the import smoke gate, and how to cut a `py-v*` release | 01 |

The measured basis for all three is in two studies written 2026-08-24 and
reproduced here as [`studies/`](studies/): the PyO3 feasibility probe (PyO3
0.29.2 compiles under this workspace's `unsafe_code = "deny"` + clippy pedantic
`-D warnings`; an abi3 wheel imports on Python 3.14.4 with no `libpython` link)
and the agentic-framework comparison (pydantic-ai 2.33.0 chosen; the reasons
and the alternatives are in the study).

## Rules this strand adds

1. **The Python surface is a projection of the Rust API.** No function exists
   in Python that does not exist in Rust; no Python call can admit a fact, write
   a ledger, relax a checker, or change an axiom footprint. Submodule = trust
   tier: `R` (read/pure), `P` (propose — untrusted search), `C` (check/replay).
   `axeyum.knowledge` is read-only by construction.
2. **`scripts/` stays standard-library-only.** Measured 2026-08-24: 640
   scripts, zero third-party imports; that is why `just check` runs on a fresh
   host. Nothing under `scripts/` may `import axeyum`. The two worlds exchange
   JSON on disk, which is already how every producer/checker pair here talks.
3. **`unknown` and `declined` are values, never exceptions.** Hard rule,
   carried across the language boundary verbatim.
4. **Every test gate prints a nonzero count.** `pytest` with zero collected
   tests, a stub drift check that compared zero files, a doctest run over zero
   examples — each is the inert-gate trap this repository has hit repeatedly,
   and the Python gate must refuse to pass on an empty run.
5. **Build through `scripts/cargo-serialized.sh`, and `TMPDIR` off `/tmp`.**
   `maturin develop` writes a wheel to `TMPDIR` per rebuild; `/tmp` here is a
   62 G RAM tmpfs already implicated in OOM kills.
6. **Agents never see held-out nursery rows.** The filter is in the tool, not
   the prompt; `check-autogenesis-holdout-isolation.py` string-walks every
   artifact, including episodes.

## Status

Lane status lives in [`docs/plan/status/python-layer.md`](../plan/status/python-layer.md)
and is emitted into `PLAN.md` by `scripts/gen-plan.py`. This folder carries the
plans; that file carries what is true now.

## Mathematica-shaped verbs

`axeyum.m` (`Simplify`, `Factor`, `Expand`, `Together`, `Solve`, `D`, `Integrate`,
`Series`, `Limit`, `N`, `TrigSimplify`) accepts strings (`"x^2 + 5 x + 6"`,
`"Sin[x]^2"`) or `Expr`, infers the variable when exactly one is free and
refuses to guess otherwise, and `show()` folds `x - (-2)` into `x + 2`. Pure
Python over `axeyum.cas`; every result keeps its Rust certificate.
