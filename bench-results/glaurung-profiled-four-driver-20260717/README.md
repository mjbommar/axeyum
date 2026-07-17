# Glaurung four-driver internal Axeyum attribution

- Date: 2026-07-17
- Glaurung revision: `403a5c5c1f6c5152fef6cefd0d78c3eb90d3888f`
- Axeyum solver revision: `4464dae2`
- Method: one diagnostic profiled four-cell process per driver
- Join unit: exact ordered occurrence plus query hash

This artifact follows ADR-0218's observational feature result with internal
Axeyum work attribution. Glaurung's existing opt-in cold and retained profiles
record translation, rewrite, bit blast, CNF encoding, SAT, model lift, replay,
model extraction, and structural deltas. The new fail-closed joiner requires
exactly one cold and one warm profile for every ordered check, accepts their
rotating order, verifies query hash/outcome/completeness, and enforces that
named phases plus unattributed time equal adapter total.

The profiles render query identities and synchronously emit JSONL inside the
outer fair cell. That overhead is large and deliberately excluded from this
artifact's interpretation. These N=1 diagnostics identify internal work; all
solver ratios below come from the separate unprofiled N=5 artifacts.

## Whole-driver mechanism map

| Driver | Unprofiled warm Z3/Axeyum | Cold AIG / clauses per check | Warm AIG / clauses added per check | Warm CNF share | Warm SAT share |
|---|---:|---:|---:|---:|---:|
| DptfDevGen | 0.7875x | 5,513 / 7,250 | 70.2 / 126.3 | 20.40% | 65.10% |
| vwififlt | 1.0030x | 5,150 / 6,371 | 13.0 / 48.6 | 11.23% | 70.32% |
| IntcSST | 1.5315x | 1,567 / 1,746 | 25.5 / 60.7 | 16.56% | 58.36% |
| SurfacePen | 1.5584x | 727 / 626 | 7.6 / 23.4 | 12.02% | 47.75% |

This explains the earlier lexical-size failure. Dptf has only a 6.1 KiB median
SMT-LIB query, yet its cold lowered structure is comparable to the much larger
vwififlt text and several times IntcSST/SurfacePen. Retention removes 98--99%
of cold per-check AIG/CNF construction on all four drivers. Once that happens,
SAT is the largest measured Axeyum phase everywhere (48--70%); another broad
construction-only thesis cannot explain the final warm solver ordering.

## UNSAT stratum

| Driver | Unprofiled UNSAT Z3/Axeyum | Warm AIG / clauses added per UNSAT | Warm UNSAT CNF share | Warm UNSAT SAT share |
|---|---:|---:|---:|---:|
| DptfDevGen | 0.3324x | 148.0 / 258.1 | 36.55% | 51.85% |
| vwififlt | 0.7887x | 19.6 / 76.3 | 36.58% | 42.44% |
| IntcSST | 0.9707x | 53.1 / 133.6 | 51.26% | 26.83% |
| SurfacePen | 2.0382x | 30.9 / 72.9 | 37.02% | 24.53% |

Dptf's losing UNSAT stratum adds the most retained AIG/CNF structure and still
spends most measured time in SAT. That selects a precise next control: compare
identical retained Dptf UNSAT CNF across Axeyum's SAT core, Z3, and a neutral
solver, while retaining CNF-addition counts as a covariate. SurfacePen proves
that low retained clause addition alone is not sufficient—its UNSAT clause
count is close to vwififlt but its solver ordering reverses.

Each driver directory contains the machine-readable aggregate `report.json`
and complete per-occurrence `occurrences.csv`. Raw traces and profile JSONL
remain outside git at their paths embedded in the reports.

Artifact SHA-256 values:

| Driver | `report.json` | `occurrences.csv` |
|---|---|---|
| DptfDevGen | `88876394e0859498448cd0d5bec84bbcfbc3f8aadcd44d8baedfbd0e38c7a534` | `fcf87bd8eb487ba4654343a8fa067572c9b441c93aa4cc008272739563160a8d` |
| vwififlt | `3195bda0be006398a454b92695f8d4ec04e05bc2ad2733c60a63962e30e736a3` | `d52768cfb5ddc0f973be313a840b63a27b8fde34b70c4c6d31a2676414e0f257` |
| IntcSST | `20145b931376833785d407f023b91427b4dfdbe4102978d8ed260c87cf4c8ced` | `0f0ae2530843530707f3cd1492e3ad23c16b77f47616e1c7a0768c0526254ed5` |
| SurfacePen | `31b3f4b3af4fad88efa5d9907ec6f4c017d4013f3984c2db7472cd9c6e8e7366` | `b31bba3d533e33ca856cdbe2a43cec82167dcf4a21af6d303af901a03ad26383` |
