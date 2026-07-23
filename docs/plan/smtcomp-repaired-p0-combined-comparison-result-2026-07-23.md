# SMT-COMP repaired P0 combined-comparison result

Status: comparison complete; harness integrated, result/status landing pending;
branch-wide format gate blocked by out-of-lane drift
Date: 2026-07-23
Plan: [combined-comparison plan](smtcomp-repaired-p0-combined-comparison-plan-2026-07-23.md)
Generated view: [combined comparison](generated/smtcomp-repaired-p0-comparison.md)

## Result

The three completed repaired-P0 external result roots now have one deterministic,
fail-closed comparison. The generator independently validates the preparation,
all generic result bundles, all three external completions, and every immutable
result record before joining benchmarks by `(benchmark_id,
benchmark_sha256)`. It writes no NAS artifact and launches no solver,
coordinator, allocation, lease, or finalizer operation.

All exact populations account completely. There are zero known-status
contradictions and zero cross-solver `sat`/`unsat` disagreements.

## Native scopes

Only `sat` and `unsat` count as decisions. `unknown` is an observed response but
not a decision; a null admitted status is `no-verdict`.

| Solver | Rows | Decisions | Known-correct | Unadjudicated decisions | `unknown` | No verdict |
|---|---:|---:|---:|---:|---:|---:|
| Axeyum | 1,810 | 914 | 905 | 9 | 280 | 616 |
| cvc5 | 1,810 | 1,513 | 1,495 | 18 | 0 | 297 |
| Bitwuzla | 1,305 | 1,221 | 1,179 | 42 | 0 | 84 |

The "known-correct" column excludes decisions on the 90 rows whose benchmark
status is absent. Those are retained separately as unadjudicated decisions.
No absent-status decision is silently relabeled as independently correct.

Per-logic decision coverage is:

| Logic | Axeyum | cvc5 | Bitwuzla |
|---|---:|---:|---:|
| QF_ABVFP (525) | 194 | 401 | 521 |
| QF_AUFLIA (505) | 253 | 503 | not in cell |
| QF_BVFP (505) | 375 | 440 | 500 |
| QF_FP (275) | 92 | 169 | 200 |

## Comparable projections

The exact 1,810-row Axeyum/cvc5 projection is:

| Both decide and agree | Axeyum only | cvc5 only | Neither | Disagree |
|---:|---:|---:|---:|---:|
| 862 | 52 | 651 | 245 | 0 |

The exact 1,305-row FP-family pairwise projections are:

| Pair | Both decide and agree | Left only | Right only | Neither | Disagree |
|---|---:|---:|---:|---:|---:|
| Axeyum / Bitwuzla | 659 | 2 | 562 | 82 | 0 |
| cvc5 / Bitwuzla | 1,007 | 3 | 214 | 81 | 0 |

The exact three-solver FP-family projection is:

| Three decide | Two decide | One decides | None decide | Disagree |
|---:|---:|---:|---:|---:|
| 609 | 448 | 169 | 79 | 0 |

Among the 169 one-decider rows, Axeyum is sole decider for 2, cvc5 for 3, and
Bitwuzla for 164. Among the 448 two-decider rows, Axeyum is the sole
non-decider for 398, cvc5 for 50, and Bitwuzla for 0.

The 505 rows outside Bitwuzla are proven to be exactly QF_AUFLIA. On that
separate Axeyum/cvc5 projection, both decide and agree on 253 rows, cvc5 alone
decides 250, neither decides 2, and there are zero disagreements.

## Bound artifacts

| Artifact | SHA-256 |
|---|---|
| Generated JSON file | `265c9176dc3fde4b1fac6d1633ac415bdec6f2a206f9a507dff6f066b5c5e1a9` |
| Generated JSON record | `68b12c47ea852720bedd4161bac37058e779dee0668125a48194c1dabb1ad2dc` |
| Generated Markdown file | `07231a7ed25612a18cc350c6245c043d211ce6013b6899f8394c77e1ecd777f2` |
| Preparation completion | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` |
| Axeyum external result record | `97f27a480f9694e97765d669823b05c34ced8825f2f598c16e00ea301b1c4a57` |
| cvc5 external result record | `e6fbc654535c82bb5d9fa9460ba802cf41d128c28778b859f990df2160a37faf` |
| Bitwuzla external result record | `7ec879514032b00ed5d8fffd119d126df90681a6b0ed4e2bf9ea737ae94df6f3` |

Implementation commit `c9e3a972` adds the pure comparator, bounded generator,
self-sealed JSON, derived Markdown, portable generated-artifact check, and
fixture/mutation coverage. The integrator subsequently landed the
preregistration and implementation through `origin/main=08c52380`.

## Gates

The following gates pass on the committed implementation:

```text
focused comparison tests: 12, OK
portable SMT-COMP gate: 87 tests, OK, one expected live-host skip
generated artifact check: OK
live three-root revalidation and generated-byte comparison: OK
links: OK
foundational resources: 137 concepts, 174 example packs, OK
git diff --check: OK
```

The later branch-wide `just check` attempt stopped at its first recipe,
`cargo fmt --all --check`, before any downstream recipe ran. The formatter
reports pre-existing drift in one bench file and eight CAS source files:

```text
crates/axeyum-bench/examples/audit_dominance.rs
crates/axeyum-cas/src/{combinatorics,gosper,lib,ntheory_advanced,
  ntheory_more,orthopoly,series,special}.rs
```

Those paths are outside this lane, are already present in the integrated base,
and were not modified or reformatted here. The SMT-specific gates above remain
green, but the topic agent does not claim a green branch-wide gate or take
ownership of the unrelated formatting repair.

The live command and a second fresh check reproduced both committed generated
files byte-identically:

```sh
python3 scripts/generate-smtcomp-repaired-p0-comparison.py \
  --preparation-root /nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2
python3 scripts/generate-smtcomp-repaired-p0-comparison.py --check \
  --preparation-root /nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2
python3 scripts/generate-smtcomp-repaired-p0-comparison.py --check
```

## Bounded conclusion and next action

This closes the repaired-P0 combined-comparison milestone. It establishes a
reproducible decision/capability map on the exact four-logic and FP-only scopes;
it does not establish a performance ranking, official competition result,
full-library result, or general parity claim. In particular, Bitwuzla's
1,305-row population is never aggregated with the two 1,810-row populations.

After integrator-controlled landing, the next measurement step is a separately
preregistered credited full-population plan with one common selection identity
for Axeyum, cvc5, and Bitwuzla. This topic agent must not merge or push `main`.
