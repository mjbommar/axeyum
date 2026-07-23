# SMT-COMP admitted slices S5.1 plan

Status: complete
Date: 2026-07-23
Depends on: [S5 harness-admission result](smtcomp-harness-admission-s5-result-2026-07-23.md)
Decision: [accepted ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)

## Gap exposed by the next milestone

S5 admits the complete 45,905-file official selection, but the next required
measurements are complete per-logic P0 slices. A second locally sampled or
unbound selection would violate ADR-0356. Running all 45,905 files merely to
measure four affected logics would violate the bounded P0 sequence.

S5.1 therefore extends the admitted v2 execution ledger to a nonempty ordered
subset of the accepted official selection. It changes no solver, scoring,
resource, checkpoint, or result semantics and authorizes no execution by
itself.

## Exact contract

For every full or subset ledger construction and preflight:

1. The complete S4 `complete.json`, `official-selected.txt`, and
   `selected-files.jsonl` identities remain bound exactly as in S5.
2. The validator streams the complete official list and complete selected-file
   ledger together and validates every canonical row, including rows outside
   the requested execution subset.
3. The execution file list must be nonempty, strictly ordered as an official-
   list subsequence, duplicate-free, and contain no unselected ID.
4. Every requested physical file is rehashed and must match its exact ledger
   byte count and SHA-256. Non-requested physical files need not be rehashed by
   this bounded slice operation; their immutable identities remain bound by
   S4 completion and the complete ledger digest.
5. The v2 manifest records only requested benchmark execution rows while its
   `official_selection` object continues to record the complete 45,905-row
   population identity.
6. A full-population invocation must remain byte-identical to the accepted S5
   v2 manifest. This extension is a strict generalization, not a schema fork.

## Preregistered rejecting mutations

| ID | Mutation |
|---|---|
| S5.1-M01 | requested execution ID is not in the official selection |
| S5.1-M02 | requested official IDs occur out of official-list order |
| S5.1-M03 | requested execution ID is duplicated |
| S5.1-M04 | a complete-ledger row outside the requested subset differs from the official list |
| S5.1-M05 | requested physical bytes differ from the selected-file row |

Each mutation rejects before a run directory exists. The existing S5-M01
through S5-M09 matrix remains green.

## Bounded P0 populations unlocked

The accepted S4 artifact fixes these exact complete slices:

| Logic | Files | Selected bytes | Relative-list SHA-256 |
|---|---:|---:|---|
| `QF_FP` | 275 | 4,748,038 | `5e5cac8fba6821ce7e8767c4a2cfcabef58a20081152660dba67d5d5a64c5cb8` |
| `QF_BVFP` | 505 | 3,333,275 | `ab85a5f52f383f109db26d1a8cc30d8e6e35b406342d1ebe135353d6a62c3d72` |
| `QF_ABVFP` | 525 | 24,428,743 | `2ee1586a2afe6539ca856655287ba654ba448c4612bccf2d32a544156bd30bde` |
| `QF_AUFLIA` | 505 | 4,485,241 | `1d2bb471f9b1363aff51f6c4929090f04d1bc164688289a6b5013517a68be6a2` |
| **Total** | **1,810** | **36,995,297** | — |

These counts describe the next planning input only. S5.1 does not launch them.

## Gates

```sh
python3 -m unittest scripts.tests.test_smtcomp_resume_runner
./scripts/check-smtcomp-resume.sh
./scripts/check-links.sh
just foundational-resources
```

After the tiny fixture passes, construct and validate one no-solver combined
1,810-file execution ledger against the accepted S4 root. Only then may a
separate P0 execution plan preregister binaries, oracles, limits, hosts, shards,
and result gates.

Completed result:
[S5.1 admitted-slice result](smtcomp-admitted-slices-s5.1-result-2026-07-23.md).
