# Reference-only file lists, 2026-09-05 (S3 loss census)

SUPERSEDED-BY: parity-losses-20260908

> **DO NOT BRIEF A LANE AGAINST THE LISTS IN THIS DIRECTORY.** Re-measured
> 2026-09-08 at the shipped default, a large fraction of these 403 files are
> already decided. The lists are correct as a record of 2026-09-05 and are kept
> byte-identical for that reason; the population to cite is
> [`../parity-losses-20260908/`](../parity-losses-20260908/), and
> `python3 scripts/check-loss-list-freshness.py` prints the per-division
> authority table. This set reads `behind=606` commits touching `crates/` as of
> 2026-09-08.

> **The `class` and `last_route` columns in the `*.census.tsv` files here are
> NOT reliable.** They were produced through `explain_corpus`, which runs the
> flat assertion view rather than the shipped front door and disagrees with it
> on 134 of 397 benchmarks, and they name the last route rather than the route
> that spent the budget. Re-measurement refuted at least 67 of 70 rows across
> QF_UF and UF. The `<DIV>.txt` populations, the wall times and the
> `smtcomp_cli` verdicts are unaffected and remain good. Full correction:
> [the census note](../../docs/research/11-design-review/2026-09-05-parity-loss-census.md).


Extracted with `awk -F'\t' 'NR>1 && $2=="unsolved" && ($3=="sat"||$3=="unsat") {print $1}'`
from the parity sidecars at `~/axeyum-parity-20260905/bench-results/parity-details/<DIV>.tsv`
on hosts s5 (QF_BV, QF_ABV, QF_UF, UF), s6 (QF_LRA, QF_IDL, QF_RDL, QF_SLIA), and s7
(QF_LIA, QF_NIA, QF_UFLIA), each a clean detached worktree at solver commit
`9914a1c0e` (`docs/plan/smt-parity-plan-2026-09-05.md` S3, §4 row S3, §6).

Each `<DIV>.txt` here is one absolute corpus path per line: the reference-only
files (reference `sat` or `unsat`, axeyum `unsolved`) for that division on the
day's sweep. Counts match `docs/plan/smt-parity-plan-2026-09-05.md` §1's
"Theirs only" column exactly:

| Division | Files | Sidecar |
|---|---:|---|
| QF_SLIA | 7 | `parity-details/QF_SLIA.tsv` (s6) |
| QF_BV | 6 | `parity-details/QF_BV.tsv` (s5) |
| UF | 32 | `parity-details/UF.tsv` (s5) |
| QF_ABV | 19 | `parity-details/QF_ABV.tsv` (s5) |
| QF_LIA | 27 | `parity-details/QF_LIA.tsv` (s7) |
| QF_UF | 38 | `parity-details/QF_UF.tsv` (s5) |
| QF_RDL | 47 | `parity-details/QF_RDL.tsv` (s6) |
| QF_UFLIA | 58 | `parity-details/QF_UFLIA.tsv` (s7) |
| QF_LRA | 54 | `parity-details/QF_LRA.tsv` (s6) |
| QF_IDL | 54 | `parity-details/QF_IDL.tsv` (s6) |
| QF_NIA | 61 | `parity-details/QF_NIA.tsv` (s7) |
| **Total** | **403** | |

The census run itself (`<DIV>.census.tsv`, one per division) classifies every
file here per `docs/research/11-design-review/2026-09-05-parity-loss-census.md`.
