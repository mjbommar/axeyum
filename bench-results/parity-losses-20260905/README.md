# Reference-only file lists, 2026-09-05 (S3 loss census)

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
