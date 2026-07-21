# SMT-COMP scoring reproduction (in-tree replica)

A from-scratch local replica of the **SMT-COMP selection and scoring rules**,
plus a bounded self-contained execution approximation, built to measure axeyum
without touching or PR-ing the public SMT-COMP repositories. The official 2026
execution layer is BenchExec; this directory does not inherit BenchExec's
resource isolation or artifact guarantees. The upstream
tooling (`SMT-COMP/smt-comp.github.io`, `scrambler`, `trace-executor`,
`benchexec`) is read as a reference only; nothing here is pushed upstream.

Specification source: **SMT-COMP 2026 Rules and Procedures** (21st competition,
revised 2026-04-11), §5 (execution), §6 (benchmark selection), §7 (scoring).
Section references in the code point at that document.

## The pipeline, stage by stage

| Stage | Rules § | Module | Status |
|---|---|---|---|
| A. Benchmark selection (per-division cap formula, seeded family sampling) | §6 | `selection.py` | **done** (scrambling = reference-only) |
| B. Resource-limited execution (wall `T`, CPU `mT`, mem; measures `aw`,`ac`) | §5 | `runner.py` | **done** (self-contained; BenchExec optional) |
| C. Result → benchmark score tuple ⟨e,n,aw,w,ac,c⟩ (all 5 tracks) | §7.1 | `scoring.py` | **done** |
| C′. Sequential benchmark score ⟨e_S,n_S,c_S⟩ (virtual CPU limit = T) | §7.1.1 | `scoring.py` | **done** |
| D. Division scoring: parallel, PAR-2, sequential, 24s, sat, unsat; disagreement removal | §7.2 | `scoring.py` | **done** |
| E. Competition-wide: Best Overall, Biggest Lead, Largest Contribution | §7.3 | `scoring.py` | **done** |
| —. End-to-end driver + local shard execution | — | `compete.py`, `run_repro.sh` | **bounded slice** |
| —. Resumable distributed execution | — | `resume_contract.py`, ADR-0344 | **contract prototype; production open** |
| —. Source-family + exact-content provenance | — | `provenance.py` | **done** |

Scoring/selection tests (42): `tests/test_scoring.py` (30, one per rule),
`tests/test_pipeline.py` (5, full aggregation/ranking),
`tests/test_selection.py` (5, §6 caps + sampling), and
`tests/test_provenance.py` (2, family normalization + exact duplicates).
Six additional generator tests exercise the 14-invariant/22-scenario resume
contract. These tests do not establish production filesystem durability.

## Reproduce

```sh
# self-contained local run (builds the axeyum CLI, scores vs cvc5 + bitwuzla):
scripts/smtcomp_repro/run_repro.sh corpus/qfbv-curated 20 40 single_query

# Small local shard experiment only. Current raw dumping is end-of-shard and
# must not be used for a large distributed run before ADR-0344 E1-E3:
python3 scripts/smtcomp_repro/compete.py --corpus corpus/qfbv-curated \
    --solver axeyum=target/release/examples/smtcomp_cli \
    --shard 0/2 --dump-raw /tmp/raw0.json ...        # local
ssh s0 'cd <repo> && python3 .../compete.py ... --shard 1/2 --dump-raw <shared>/raw1.json ...'
python3 scripts/smtcomp_repro/compete.py --score-raw /tmp/raw0.json <shared>/raw1.json
```

The failed full-tree attempt and required replacement protocol are documented
in the
[`full-library handoff`](../../docs/plan/smtcomp-full-library-candidate-run-handoff-2026-07-21.md)
and generated
[`resumable-run contract`](../../docs/plan/generated/smtcomp-resumable-run-contract.md).

## Tracks

Single Query, Incremental, Unsat-Core, Model-Validation, Parallel — the tuple
rules for each live in `scoring.py::benchmark_score`.

## Fidelity checks

- Unit tests (`tests/`) hand-verify every tuple/ordering/ranking rule.
- Cross-validation: synthetic result tables scored here vs. the official
  `smtcomp` tool (cloned into gitignored `references/`), see `xcheck/`.

## Not upstream

This directory never opens a PR against SMT-COMP. It is our private measuring
tape.
