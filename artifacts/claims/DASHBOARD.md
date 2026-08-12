# Claim Ledger Dashboard

> **Auto-generated. Do not edit by hand.** Regenerate with `python3 scripts/gen-claims-dashboard.py`.

One row per claim under `artifacts/claims/<family>/<id>/claim.json`: what is asserted, how firmly it is believed, and which evidence rows carry it. Every value is read straight from a committed claim file — nothing here is recomputed. The ledger's vocabulary and gates are described in [`README.md`](README.md) ([ADR-0380](../../docs/research/09-decisions/adr-0380-claim-ledger.md)).

`check_status` is per evidence row, not per claim: `checked` means `scripts/check-claim-certificates.py` re-derives it independently, `replay-only` means the artifact replays but no certificate exists, and `not-checked` marks an honest citation or unverified support.

## Summary

- Claims: 38 across 1 family (`rado` 38)
- Epistemic status: `computed` 36, `open` 2
- Evidence rows: 81 — `checked` 77, `replay-only` 4
- Evidence kinds: `cube-cover` 6, `unsat-certificate` 35, `witness-replay` 40
- Concept references: 190 — 152 resolved, 38 pending
- Frontier records (open/conjectured claims): 2

## Claims

### `rado`

| Claim | Title | Status | Evidence (kind: check_status) | Refs resolved | Refs pending |
| --- | --- | --- | --- | ---: | ---: |
| [`rado-r3-a1-b1`](rado/rado-r3-a1-b1/claim.json) | R_3(1(x-y)=1z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a1-b2`](rado/rado-r3-a1-b2/claim.json) | R_3(1(x-y)=2z) = 43 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a1-b3`](rado/rado-r3-a1-b3/claim.json) | R_3(1(x-y)=3z) = 94 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a1-b4`](rado/rado-r3-a1-b4/claim.json) | R_3(1(x-y)=4z) = 173 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a1-b5`](rado/rado-r3-a1-b5/claim.json) | R_3(1(x-y)=5z) = 286 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a2-b1`](rado/rado-r3-a2-b1/claim.json) | R_3(2(x-y)=1z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a2-b2`](rado/rado-r3-a2-b2/claim.json) | R_3(2(x-y)=2z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a2-b3`](rado/rado-r3-a2-b3/claim.json) | R_3(2(x-y)=3z) = 61 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a2-b4`](rado/rado-r3-a2-b4/claim.json) | R_3(2(x-y)=4z) = 43 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a2-b5`](rado/rado-r3-a2-b5/claim.json) | R_3(2(x-y)=5z) = 181 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a3-b1`](rado/rado-r3-a3-b1/claim.json) | R_3(3(x-y)=1z) = 27 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a3-b2`](rado/rado-r3-a3-b2/claim.json) | R_3(3(x-y)=2z) = 31 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a3-b3`](rado/rado-r3-a3-b3/claim.json) | R_3(3(x-y)=3z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a3-b4`](rado/rado-r3-a3-b4/claim.json) | R_3(3(x-y)=4z) = 109 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a3-b5`](rado/rado-r3-a3-b5/claim.json) | R_3(3(x-y)=5z) = 186 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a4-b1`](rado/rado-r3-a4-b1/claim.json) | R_3(4(x-y)=1z) = 64 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a4-b2`](rado/rado-r3-a4-b2/claim.json) | R_3(4(x-y)=2z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a4-b3`](rado/rado-r3-a4-b3/claim.json) | R_3(4(x-y)=3z) = 73 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a4-b4`](rado/rado-r3-a4-b4/claim.json) | R_3(4(x-y)=4z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a4-b5`](rado/rado-r3-a4-b5/claim.json) | R_3(4(x-y)=5z) = 180 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a5-b1`](rado/rado-r3-a5-b1/claim.json) | R_3(5(x-y)=1z) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a5-b2`](rado/rado-r3-a5-b2/claim.json) | R_3(5(x-y)=2z) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a5-b3`](rado/rado-r3-a5-b3/claim.json) | R_3(5(x-y)=3z) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a5-b4`](rado/rado-r3-a5-b4/claim.json) | R_3(5(x-y)=4z) = 141 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r3-a5-b5`](rado/rado-r3-a5-b5/claim.json) | R_3(5(x-y)=5z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a1-b1`](rado/rado-r4-a1-b1/claim.json) | R_4(1(x-y)=1z) = 45 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a1-b2`](rado/rado-r4-a1-b2/claim.json) | R_4(1(x-y)=2z) = 171 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a2-b1`](rado/rado-r4-a2-b1/claim.json) | R_4(2(x-y)=1z) = 56 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`cube-cover`: checked | 4 | 1 |
| [`rado-r4-a2-b2`](rado/rado-r4-a2-b2/claim.json) | R_4(2(x-y)=2z) = 45 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a2-b3`](rado/rado-r4-a2-b3/claim.json) | R_4(2(x-y)=3z) = 226 | `computed` | `witness-replay`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: replay-only<br>`cube-cover`: checked | 4 | 1 |
| [`rado-r4-a3-b1`](rado/rado-r4-a3-b1/claim.json) | R_4(3(x-y)=1z) = 81 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a3-b2`](rado/rado-r4-a3-b2/claim.json) | R_4(3(x-y)=2z) = 103 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a3-b3`](rado/rado-r4-a3-b3/claim.json) | R_4(3(x-y)=3z) = 45 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a4-b1`](rado/rado-r4-a4-b1/claim.json) | R_4(4(x-y)=1z) = 256 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a4-b2`](rado/rado-r4-a4-b2/claim.json) | R_4(4(x-y)=2z) = 56 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 | 1 |
| [`rado-r4-a4-b3`](rado/rado-r4-a4-b3/claim.json) | R_4(4(x-y)=3z) = 313 | `computed` | `witness-replay`: checked<br>`cube-cover`: replay-only<br>`cube-cover`: replay-only<br>`cube-cover`: replay-only<br>`cube-cover`: checked | 4 | 1 |
| [`rado-r4-a5-b4-frontier`](rado/rado-r4-a5-b4-frontier/claim.json) | R_4(5(x-y)=4z) > 740: the shell construction's largest four-colour prediction | `open` | `witness-replay`: checked | 4 | 1 |
| [`rado-r5-a3-b2-frontier`](rado/rado-r5-a3-b2-frontier/claim.json) | R_5(3(x-y)=2z) > 350: first five-colour bound for this family | `open` | `witness-replay`: checked<br>`witness-replay`: checked | 4 | 1 |

## Frontier

Open and conjectured claims carry a mandatory `frontier` record: what is currently known, and the concrete artifact that would settle the claim. These are the ledger's work items.

### `rado-r4-a5-b4-frontier` — R_4(5(x-y)=4z) > 740: the shell construction's largest four-colour prediction

- Status: `open`
- Claim: [`rado/rado-r4-a5-b4-frontier/claim.json`](rado/rado-r4-a5-b4-frontier/claim.json)

**Known**

- R_4(5(x-y)=4z) > 740, witnessed and verified (evidence row witness-740)
- The shell construction predicts 741 exactly; tightness holds at all four k<=4 points previously tested ((3,3) [31], (4,3) [73], (3,4) [103], (4,4) [313]) and fails at k=5 (see rado-r5-a3-b2-frontier)
- Min-conflicts SLS from a warm start at the [740] witness found NO 4-colouring of [741] in 4 independent seeded runs of 30M moves each (s7, 2026-08-12) - consistent with 741 being exact, and in contrast to the k=5 case where SLS found the refuting witness in seconds
- A depth-6 cube-cover probe of F_741 (4096 cells over branch points 2,4,6,8,10,12) shows the mass of cells refute by unit propagation instantly while staircase-compatible cells exhaust a 200k-conflict budget in ~8.5 s each: the refutation is search-hard, as the roadmap predicted, and needs deeper adaptive splitting plus fleet time

**Would settle:** An exhaustive cube cover refuting [741], every cell's DRAT proof checked by axeyum's own backward checker - exactly the artifact pair that certified 226 and 313. The witness half is already done.

**Attack notes:** The satisfiable side is closed (the construction hands over the witness free). For the refutation, reuse the 313 recipe at greater depth: branch on more points (depth 8-10), cap per-cell conflicts, defer checking, and certify offline with certify_dumped_cover; distribute cells across s5-s7. The probe suggests concentrating splits inside the staircase-compatible subtree rather than uniformly.

### `rado-r5-a3-b2-frontier` — R_5(3(x-y)=2z) > 350: first five-colour bound for this family

- Status: `open`
- Claim: [`rado/rado-r5-a3-b2-frontier/claim.json`](rado/rado-r5-a3-b2-frontier/claim.json)

**Known**

- R_5(3(x-y)=2z) > 350, witnessed and verified (evidence row witness-350); the earlier 319 witness is retained as the point that refuted tightness
- The shell construction of this work yields a verified solution-free colouring of [N] with N+1 = a^k + a^(k-1) - 2a + 1; this is ATTAINED at (a,k)=(3,3) [31], (4,3) [73], (3,4) [103] and (4,4) [313], all independently re-verified, but NOT at (3,5), where it gives 318 while a 5-colouring of [319] exists. The general-k proof is asserted in the construction source and has NOT been independently verified here.
- Independent corroboration of k=5 non-tightness in a different column: Li (SSRN 6814341) reports R_5(3)>296>243 for b=1
- The incremental climb stalled at 351 after warm-restart retries; that is a search limit, not evidence of a threshold

**Would settle:** A verified 5-colouring of [n-1] together with an exhaustive cube cover refuting [n], for the same n. Both artifact kinds and their checkers exist in this family; the obstruction is the cost of refutation at k=5, not the encoding.

**Attack notes:** The satisfiable side is cheap here (14.8 s by cube search, 32.3 s by monolithic CDCL), so the lower bound can be pushed far. The refutation side at five colours is untested at any n and is the real question.

## Provenance

Generated by [`scripts/gen-claims-dashboard.py`](../../scripts/gen-claims-dashboard.py) from the following committed claim files (deterministic — no timestamps, fully sorted; re-running on unchanged claims yields a byte-identical file):

- `artifacts/claims/rado/rado-r3-a1-b1/claim.json`
- `artifacts/claims/rado/rado-r3-a1-b2/claim.json`
- `artifacts/claims/rado/rado-r3-a1-b3/claim.json`
- `artifacts/claims/rado/rado-r3-a1-b4/claim.json`
- `artifacts/claims/rado/rado-r3-a1-b5/claim.json`
- `artifacts/claims/rado/rado-r3-a2-b1/claim.json`
- `artifacts/claims/rado/rado-r3-a2-b2/claim.json`
- `artifacts/claims/rado/rado-r3-a2-b3/claim.json`
- `artifacts/claims/rado/rado-r3-a2-b4/claim.json`
- `artifacts/claims/rado/rado-r3-a2-b5/claim.json`
- `artifacts/claims/rado/rado-r3-a3-b1/claim.json`
- `artifacts/claims/rado/rado-r3-a3-b2/claim.json`
- `artifacts/claims/rado/rado-r3-a3-b3/claim.json`
- `artifacts/claims/rado/rado-r3-a3-b4/claim.json`
- `artifacts/claims/rado/rado-r3-a3-b5/claim.json`
- `artifacts/claims/rado/rado-r3-a4-b1/claim.json`
- `artifacts/claims/rado/rado-r3-a4-b2/claim.json`
- `artifacts/claims/rado/rado-r3-a4-b3/claim.json`
- `artifacts/claims/rado/rado-r3-a4-b4/claim.json`
- `artifacts/claims/rado/rado-r3-a4-b5/claim.json`
- `artifacts/claims/rado/rado-r3-a5-b1/claim.json`
- `artifacts/claims/rado/rado-r3-a5-b2/claim.json`
- `artifacts/claims/rado/rado-r3-a5-b3/claim.json`
- `artifacts/claims/rado/rado-r3-a5-b4/claim.json`
- `artifacts/claims/rado/rado-r3-a5-b5/claim.json`
- `artifacts/claims/rado/rado-r4-a1-b1/claim.json`
- `artifacts/claims/rado/rado-r4-a1-b2/claim.json`
- `artifacts/claims/rado/rado-r4-a2-b1/claim.json`
- `artifacts/claims/rado/rado-r4-a2-b2/claim.json`
- `artifacts/claims/rado/rado-r4-a2-b3/claim.json`
- `artifacts/claims/rado/rado-r4-a3-b1/claim.json`
- `artifacts/claims/rado/rado-r4-a3-b2/claim.json`
- `artifacts/claims/rado/rado-r4-a3-b3/claim.json`
- `artifacts/claims/rado/rado-r4-a4-b1/claim.json`
- `artifacts/claims/rado/rado-r4-a4-b2/claim.json`
- `artifacts/claims/rado/rado-r4-a4-b3/claim.json`
- `artifacts/claims/rado/rado-r4-a5-b4-frontier/claim.json`
- `artifacts/claims/rado/rado-r5-a3-b2-frontier/claim.json`

Regenerate with `python3 scripts/gen-claims-dashboard.py`.
