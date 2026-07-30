# String corpus provenance — Kaluza, PyEx, and what can be credited

**Date:** 2026-07-30
**Why:** the `agent/solver/qfslia-regex-length-next` branch justifies its work with
**Kaluza +262** and **PyEx +69** rows. Landing its regex-membership half
([`c7123d34`](../../STATUS.md)) required deciding whether those numbers could be
credited. They cannot, and this records exactly why, so the question is not
re-opened by guesswork.

## 1. Neither population is in the staged library

Checked directly against
`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/`, the complete
string-logic family list is:

| Logic | Families |
|---|---|
| QF_S | `2019-Jiang`, `2020-sygus-qgen`, `20230329-automatark-lu`, `20230329-woorpje-lu`, `20240318-omark` |
| QF_SLIA | `2015-Norn`, `2018-Kepler`, `20180523-Reynolds`, `2019-Jiang`, `2019-Leetcode`, `2019-full_str_int`, `20190311-str-small-rw-Noetzli`, `20230327-stringfuzz-lu`, `20230329-denghang`, `20230329-woorpje-lu`, `20230331-transducer-plus`, `20230403-webapp`, `20240411-redos_attack_detection` |
| QF_SNIA | `20180523-Reynolds`, `20200224-Wu-PyExZ3` |

- **Kaluza is absent entirely.** No family under any string logic.
- **`QF_SNIA/20200224-Wu-PyExZ3` is not the PyEx string set.** It is **5 files**
  and contains **no `str.*` operator at all** — a nonlinear-integer set from the
  same author. It is not the "fixed 2,535-file PyEx selection" the lane's reports
  reference.

So the branch's headline numbers are unverifiable on this host, and the landing
was credited only for what *is* measurable: zero movement and zero loss on
QF_SLIA 25/50, QF_S 93/134, QF_SEQ 22/33, and 296/300 on a
`20230327-stringfuzz-lu` sample, DISAGREE = 0 throughout.

## 2. Both are obtainable — as third-party research artifacts, not SMT-LIB

They are published on the **Z3str solver's benchmarks page**
(<https://sites.google.com/site/z3strsolver/benchmarks>), which offers:

| Suite | Archive |
|---|---|
| **Kaluza** | ZIP, 35 MB (Google Drive) |
| **PyEx** | ZIP, 31 MB (Google Drive) |
| IBM PISA | ZIP, 5 KB |
| IBM AppScan | ZIP, 4 KB |
| StringFuzz | external link |

Independent scale check: the literature puts Kaluza at **47,284 tests, of which
38,043 (80.4 %) are in the string-constraint fragment**.

This reframes the task. It is not a search failure — it is an **acquisition
decision**: pulling ~66 MB of third-party benchmark data from Google Drive is an
outward-facing fetch of someone else's artifacts, and it should be a deliberate
choice rather than a side effect of chasing a number.

## 3. The format gap, which is the part that actually matters

The page states the benchmarks are **"provided in SMT-LIB 2.5 format, following
the latest draft of the theory for strings."**

This repository works in **SMT-LIB 2.6**, and the string theory changed between
the two — including operator spellings (`str.to.int` → `str.to_int`) and
semantics for several operators. So:

- These corpora need a vetted **2.5 → 2.6 translation** before any number from
  them is comparable to a SCOREBOARD row.
- A translation step is itself a place a wrong verdict can hide, and the project
  already has the discipline for this: the parse/write round-trip is how the
  QF_AUFLIA P0 ruled out a parser artifact.
- **The lane's claimed +262 / +69 were plausibly measured against 2.5-era
  inputs.** That does not make them wrong, but it means they are not
  automatically comparable to anything in `bench-results/baselines/`, which is a
  second independent reason not to quote them.

## 4. Also noted: the staged library is a release behind

The measurement backbone is built on **SMT-LIB 2024**
([Zenodo 11061097](https://zenodo.org/records/11061097)). **SMT-LIB 2025** is
published ([Zenodo 15493090](https://zenodo.org/records/15493090)), and the
SMT-COMP figures already recorded in
[`smtcomp-2025-parity-targets-2026-07-28.md`](smtcomp-2025-parity-targets-2026-07-28.md)
show QF_S grew from 8,867 to 10,428 benchmarks between the two competition years.

That is a Lane D input, not a strings input: any credited full-library run should
decide deliberately which release it describes, and say so in the artifact.

## 5. Decision

**Do not acquire on a whim, and do not quote the numbers.** Concretely:

1. No Kaluza or PyEx figure from `agent/solver/qfslia-regex-length-next` may
   appear in `STATUS.md`, `SCOREBOARD.md`, or any result note until the corpora
   are committed as curated slices with manifests and re-measured here.
2. The branch's remaining `parse.rs` UNSAT families stay unlanded. Their entire
   justification is those two populations, so landing them would mean landing
   UNSAT-producing surface on unverifiable evidence — the opposite of the
   crediting discipline the rest of this work followed.
3. If the corpora are acquired, the order is: fetch → vet and translate 2.5 → 2.6
   with a round-trip check → commit as curated slices with manifests → measure →
   only then credit.

## Sources

- Z3str benchmarks page: <https://sites.google.com/site/z3strsolver/benchmarks>
- SMT-LIB 2024 non-incremental release: <https://zenodo.org/records/11061097>
- SMT-LIB 2025 non-incremental release: <https://zenodo.org/records/15493090>
- Kaluza scale figure: OSTRICH2, <https://arxiv.org/abs/2506.14363>
