# Lane: three-domain-dominance-verification

**Status:** in progress (started 2026-08-31)

## Mission

Produce ONE referee-checkable verification document for the Pareto-dominance
claim across three domains (real analysis, number theory, linear algebra).
Verification, not advocacy: where the claim does not hold, say so.

## Landed changes

| when | what |
| --- | --- |
| 2026-08-31 | lane opened; kernel examples built `--release`; holdout isolation PASS before work |

## Notes in flight

- `python3 scripts/check-autogenesis-holdout-isolation.py` BEFORE work:
  `held_out=146|files_scanned=1110|settled=0|references=0|verdict=PASS`, exit 0.
- Brief cited **ADR-1010** as "the LUB row-2 counterexample". No file matching
  `adr-1010*` exists in `docs/research/09-decisions/` at my base commit
  (`878c285d9`). Highest ADR present: 1025. To be resolved before citing.
- Kernel examples built at `--release` (57 s): `prelude_theorem_inventory`,
  `theorem_axiom_footprint`, `shape_search`, `nat_axiom_inventory`.
- ADR-1030 confirmed free at base commit.
