# Claim Ledger Dashboard

> **Auto-generated. Do not edit by hand.** Regenerate with `python3 scripts/gen-claims-dashboard.py`.

One row per claim under `artifacts/claims/<family>/<id>/claim.json`: what is asserted, how firmly it is believed, and which evidence rows carry it. Every value is read straight from a committed claim file — nothing here is recomputed. The ledger's vocabulary and gates are described in [`README.md`](README.md) ([ADR-0380](../../docs/research/09-decisions/adr-0380-claim-ledger.md)).

`check_status` is per evidence row, not per claim: `checked` means `scripts/check-claim-certificates.py` re-derives it independently, `replay-only` means the artifact replays but no certificate exists, and `not-checked` marks an honest citation or unverified support.

## Summary

- Claims: 104 across 3 families (`offdiag-schur` 48, `rado` 43, `vdw` 13)
- Epistemic status: `computed` 101, `open` 3
- Evidence rows: 269 — `checked` 265, `not-checked` 1, `replay-only` 3
- Evidence kinds: `cube-cover` 6, `cube-tree-cover` 1, `instance-pin` 52, `unsat-certificate` 100, `witness-replay` 110
- Topic citations: 438 — unresolved by design (ADR-0553); nothing in this repository resolves them
- Frontier records (open/conjectured claims): 3

## Claims

### `offdiag-schur`

| Claim | Title | Status | Evidence (kind: check_status) | Citations |
| --- | --- | --- | --- | ---: |
| [`offdiag-schur-3-3-3-10`](offdiag-schur/offdiag-schur-3-3-3-10/claim.json) | S(3;3,3,10) = 77 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-3-11`](offdiag-schur/offdiag-schur-3-3-3-11/claim.json) | S(3;3,3,11) = 86 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-3-12`](offdiag-schur/offdiag-schur-3-3-3-12/claim.json) | S(3;3,3,12) = 94 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-3-13`](offdiag-schur/offdiag-schur-3-3-3-13/claim.json) | S(3;3,3,13) = 104 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-3-14`](offdiag-schur/offdiag-schur-3-3-3-14/claim.json) | S(3;3,3,14) = 113 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-3-8`](offdiag-schur/offdiag-schur-3-3-3-8/claim.json) | S(3;3,3,8) = 59 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-3-9`](offdiag-schur/offdiag-schur-3-3-3-9/claim.json) | S(3;3,3,9) = 68 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-4-10`](offdiag-schur/offdiag-schur-3-3-4-10/claim.json) | S(3;3,4,10) = 86 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-4-11`](offdiag-schur/offdiag-schur-3-3-4-11/claim.json) | S(3;3,4,11) = 98 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-4-12`](offdiag-schur/offdiag-schur-3-3-4-12/claim.json) | S(3;3,4,12) = 106 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-4-8`](offdiag-schur/offdiag-schur-3-3-4-8/claim.json) | S(3;3,4,8) = 67 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-4-9`](offdiag-schur/offdiag-schur-3-3-4-9/claim.json) | S(3;3,4,9) = 78 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-5-8`](offdiag-schur/offdiag-schur-3-3-5-8/claim.json) | S(3;3,5,8) = 91 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-3-5-9`](offdiag-schur/offdiag-schur-3-3-5-9/claim.json) | S(3;3,5,9) = 103 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-10`](offdiag-schur/offdiag-schur-3-4-4-10/claim.json) | S(3;4,4,10) = 109 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-11`](offdiag-schur/offdiag-schur-3-4-4-11/claim.json) | S(3;4,4,11) = 120 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-12`](offdiag-schur/offdiag-schur-3-4-4-12/claim.json) | S(3;4,4,12) = 131 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-13`](offdiag-schur/offdiag-schur-3-4-4-13/claim.json) | S(3;4,4,13) = 142 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-4-4-4`](offdiag-schur/offdiag-schur-3-4-4-4/claim.json) | S(3;4,4,4) = 43 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-5`](offdiag-schur/offdiag-schur-3-4-4-5/claim.json) | S(3;4,4,5) = 54 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-6`](offdiag-schur/offdiag-schur-3-4-4-6/claim.json) | S(3;4,4,6) = 65 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-7`](offdiag-schur/offdiag-schur-3-4-4-7/claim.json) | S(3;4,4,7) = 76 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-8`](offdiag-schur/offdiag-schur-3-4-4-8/claim.json) | S(3;4,4,8) = 87 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-4-9`](offdiag-schur/offdiag-schur-3-4-4-9/claim.json) | S(3;4,4,9) = 98 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-5-10`](offdiag-schur/offdiag-schur-3-4-5-10/claim.json) | S(3;4,5,10) = 139 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-4-5-11`](offdiag-schur/offdiag-schur-3-4-5-11/claim.json) | S(3;4,5,11) = 153 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-4-5-5`](offdiag-schur/offdiag-schur-3-4-5-5/claim.json) | S(3;4,5,5) = 69 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-5-6`](offdiag-schur/offdiag-schur-3-4-5-6/claim.json) | S(3;4,5,6) = 83 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-5-7`](offdiag-schur/offdiag-schur-3-4-5-7/claim.json) | S(3;4,5,7) = 97 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-5-8`](offdiag-schur/offdiag-schur-3-4-5-8/claim.json) | S(3;4,5,8) = 111 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-5-9`](offdiag-schur/offdiag-schur-3-4-5-9/claim.json) | S(3;4,5,9) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-6-6`](offdiag-schur/offdiag-schur-3-4-6-6/claim.json) | S(3;4,6,6) = 101 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-6-7`](offdiag-schur/offdiag-schur-3-4-6-7/claim.json) | S(3;4,6,7) = 118 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-4-6-8`](offdiag-schur/offdiag-schur-3-4-6-8/claim.json) | S(3;4,6,8) = 135 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-4-6-9`](offdiag-schur/offdiag-schur-3-4-6-9/claim.json) | S(3;4,6,9) = 152 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-4-7-7`](offdiag-schur/offdiag-schur-3-4-7-7/claim.json) | S(3;4,7,7) = 139 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-4-7-8`](offdiag-schur/offdiag-schur-3-4-7-8/claim.json) | S(3;4,7,8) = 159 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-5-5`](offdiag-schur/offdiag-schur-3-5-5-5/claim.json) | S(3;5,5,5) = 94 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-5-5-6`](offdiag-schur/offdiag-schur-3-5-5-6/claim.json) | S(3;5,5,6) = 113 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`instance-pin`: checked | 4 |
| [`offdiag-schur-3-5-5-7`](offdiag-schur/offdiag-schur-3-5-5-7/claim.json) | S(3;5,5,7) = 132 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-5-8`](offdiag-schur/offdiag-schur-3-5-5-8/claim.json) | S(3;5,5,8) = 151 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-5-9`](offdiag-schur/offdiag-schur-3-5-5-9/claim.json) | S(3;5,5,9) = 170 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-6-6`](offdiag-schur/offdiag-schur-3-5-6-6/claim.json) | S(3;5,6,6) = 137 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-6-7`](offdiag-schur/offdiag-schur-3-5-6-7/claim.json) | S(3;5,6,7) = 160 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-6-8`](offdiag-schur/offdiag-schur-3-5-6-8/claim.json) | S(3;5,6,8) = 183 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-5-7-7`](offdiag-schur/offdiag-schur-3-5-7-7/claim.json) | S(3;5,7,7) = 188 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-6-6-6`](offdiag-schur/offdiag-schur-3-6-6-6/claim.json) | S(3;6,6,6) = 173 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |
| [`offdiag-schur-3-6-6-7`](offdiag-schur/offdiag-schur-3-6-6-7/claim.json) | S(3;6,6,7) = 202 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 4 |

### `rado`

| Claim | Title | Status | Evidence (kind: check_status) | Citations |
| --- | --- | --- | --- | ---: |
| [`rado-r3-a1-b1`](rado/rado-r3-a1-b1/claim.json) | R_3(1(x-y)=1z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a1-b2`](rado/rado-r3-a1-b2/claim.json) | R_3(1(x-y)=2z) = 43 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a1-b3`](rado/rado-r3-a1-b3/claim.json) | R_3(1(x-y)=3z) = 94 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a1-b4`](rado/rado-r3-a1-b4/claim.json) | R_3(1(x-y)=4z) = 173 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a1-b5`](rado/rado-r3-a1-b5/claim.json) | R_3(1(x-y)=5z) = 286 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a2-b1`](rado/rado-r3-a2-b1/claim.json) | R_3(2(x-y)=1z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a2-b2`](rado/rado-r3-a2-b2/claim.json) | R_3(2(x-y)=2z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a2-b3`](rado/rado-r3-a2-b3/claim.json) | R_3(2(x-y)=3z) = 61 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a2-b4`](rado/rado-r3-a2-b4/claim.json) | R_3(2(x-y)=4z) = 43 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a2-b5`](rado/rado-r3-a2-b5/claim.json) | R_3(2(x-y)=5z) = 181 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a3-b1`](rado/rado-r3-a3-b1/claim.json) | R_3(3(x-y)=1z) = 27 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a3-b2`](rado/rado-r3-a3-b2/claim.json) | R_3(3(x-y)=2z) = 31 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a3-b3`](rado/rado-r3-a3-b3/claim.json) | R_3(3(x-y)=3z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a3-b4`](rado/rado-r3-a3-b4/claim.json) | R_3(3(x-y)=4z) = 109 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a3-b5`](rado/rado-r3-a3-b5/claim.json) | R_3(3(x-y)=5z) = 186 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a4-b1`](rado/rado-r3-a4-b1/claim.json) | R_3(4(x-y)=1z) = 64 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a4-b2`](rado/rado-r3-a4-b2/claim.json) | R_3(4(x-y)=2z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a4-b3`](rado/rado-r3-a4-b3/claim.json) | R_3(4(x-y)=3z) = 73 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a4-b4`](rado/rado-r3-a4-b4/claim.json) | R_3(4(x-y)=4z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a4-b5`](rado/rado-r3-a4-b5/claim.json) | R_3(4(x-y)=5z) = 180 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a5-b1`](rado/rado-r3-a5-b1/claim.json) | R_3(5(x-y)=1z) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a5-b2`](rado/rado-r3-a5-b2/claim.json) | R_3(5(x-y)=2z) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a5-b3`](rado/rado-r3-a5-b3/claim.json) | R_3(5(x-y)=3z) = 125 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a5-b4`](rado/rado-r3-a5-b4/claim.json) | R_3(5(x-y)=4z) = 141 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r3-a5-b5`](rado/rado-r3-a5-b5/claim.json) | R_3(5(x-y)=5z) = 14 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a1-b1`](rado/rado-r4-a1-b1/claim.json) | R_4(1(x-y)=1z) = 45 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a1-b2`](rado/rado-r4-a1-b2/claim.json) | R_4(1(x-y)=2z) = 171 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a2-b1`](rado/rado-r4-a2-b1/claim.json) | R_4(2(x-y)=1z) = 56 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked<br>`cube-cover`: checked | 5 |
| [`rado-r4-a2-b2`](rado/rado-r4-a2-b2/claim.json) | R_4(2(x-y)=2z) = 45 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a2-b3`](rado/rado-r4-a2-b3/claim.json) | R_4(2(x-y)=3z) = 226 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked<br>`cube-cover`: checked | 5 |
| [`rado-r4-a3-b1`](rado/rado-r4-a3-b1/claim.json) | R_4(3(x-y)=1z) = 81 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a3-b2`](rado/rado-r4-a3-b2/claim.json) | R_4(3(x-y)=2z) = 103 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a3-b3`](rado/rado-r4-a3-b3/claim.json) | R_4(3(x-y)=3z) = 45 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a4-b1`](rado/rado-r4-a4-b1/claim.json) | R_4(4(x-y)=1z) = 256 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a4-b2`](rado/rado-r4-a4-b2/claim.json) | R_4(4(x-y)=2z) = 56 | `computed` | `witness-replay`: checked<br>`unsat-certificate`: checked | 5 |
| [`rado-r4-a4-b3`](rado/rado-r4-a4-b3/claim.json) | R_4(4(x-y)=3z) = 313 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`cube-cover`: checked<br>`unsat-certificate`: checked<br>`cube-cover`: replay-only<br>`cube-cover`: replay-only<br>`cube-cover`: replay-only | 5 |
| [`rado-r4-a5-b1`](rado/rado-r4-a5-b1/claim.json) | R_4(5(x-y)=1z) = 625 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`rado-r4-a5-b2`](rado/rado-r4-a5-b2/claim.json) | R_4(5(x-y)=2z) = 625 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`rado-r4-a5-b3`](rado/rado-r4-a5-b3/claim.json) | R_4(5(x-y)=3z) = 625 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`rado-r4-a5-b4-frontier`](rado/rado-r4-a5-b4-frontier/claim.json) | R_4(5(x-y)=4z) = 741 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`cube-tree-cover`: checked | 5 |
| [`rado-r4-a6-b5-frontier`](rado/rado-r4-a6-b5-frontier/claim.json) | R_4(6(x-y)=5z) > 1500: the shell construction at the next point of the k=4 row | `open` | `witness-replay`: checked | 5 |
| [`rado-r5-a3-b1-frontier`](rado/rado-r5-a3-b1-frontier/claim.json) | R_5(3(x-y)=1z) > 296: Li's public witness independently replayed | `open` | `witness-replay`: checked<br>`instance-pin`: checked<br>`witness-replay`: checked<br>`witness-replay`: checked | 3 |
| [`rado-r5-a3-b2-frontier`](rado/rado-r5-a3-b2-frontier/claim.json) | R_5(3(x-y)=2z) > 358: checked five-colour frontier bound | `open` | `witness-replay`: checked<br>`witness-replay`: checked<br>`witness-replay`: checked<br>`witness-replay`: checked | 5 |

### `vdw`

| Claim | Title | Status | Evidence (kind: check_status) | Citations |
| --- | --- | --- | --- | ---: |
| [`vdw-2-3-10`](vdw/vdw-2-3-10/claim.json) | w(2;3,10) = 97 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-11`](vdw/vdw-2-3-11/claim.json) | w(2;3,11) = 114 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-12`](vdw/vdw-2-3-12/claim.json) | w(2;3,12) = 135 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: not-checked | 3 |
| [`vdw-2-3-3`](vdw/vdw-2-3-3/claim.json) | W(2,3) = 9 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-4`](vdw/vdw-2-3-4/claim.json) | w(2;3,4) = 18 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-5`](vdw/vdw-2-3-5/claim.json) | w(2;3,5) = 22 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-6`](vdw/vdw-2-3-6/claim.json) | w(2;3,6) = 32 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-7`](vdw/vdw-2-3-7/claim.json) | w(2;3,7) = 46 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-8`](vdw/vdw-2-3-8/claim.json) | w(2;3,8) = 58 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-3-9`](vdw/vdw-2-3-9/claim.json) | w(2;3,9) = 77 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-4-4`](vdw/vdw-2-4-4/claim.json) | W(2,4) = 35 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-2-5-5`](vdw/vdw-2-5-5/claim.json) | W(2,5) = 178 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |
| [`vdw-3-3-3-3`](vdw/vdw-3-3-3-3/claim.json) | W(3,3) = 27 | `computed` | `instance-pin`: checked<br>`witness-replay`: checked<br>`unsat-certificate`: checked | 3 |

## Frontier

Open and conjectured claims carry a mandatory `frontier` record: what is currently known, and the concrete artifact that would settle the claim. These are the ledger's work items.

### `rado-r4-a6-b5-frontier` — R_4(6(x-y)=5z) > 1500: the shell construction at the next point of the k=4 row

- Status: `open`
- Claim: [`rado/rado-r4-a6-b5-frontier/claim.json`](rado/rado-r4-a6-b5-frontier/claim.json)

**Known**

- R_4(6(x-y)=5z) > 1500, witnessed and verified (evidence row witness-1500)
- The lower bound follows from this work's main theorem with no search, the hypotheses b < a and gcd(a,b) = 1 both holding at (6,5)
- The shell construction predicts 1501 exactly; tightness holds at every known point on the line b = a-1 with a >= 3 and k in {3,4}, and FAILS at k = 5 (see rado-r5-a3-b2-frontier), so the prediction is a pattern and not a theorem

**Would settle:** A refutation of F_1501 (the CNF for n = 1501, k = 4) would give R_4(6(x-y)=5z) = 1501 exactly and complete the k=4 row of the paper's Table 1. Not attempted here: F_313 already required ~28 GiB and a 4096-cell cube cover, and n = 1501 is substantially larger.

**Attack notes:** The satisfiable side is closed (the construction hands over the witness free). For the refutation, reuse the 313 recipe at greater depth: branch on more points (depth 8-10), cap per-cell conflicts, defer checking, and certify offline with certify_dumped_cover; distribute cells across s5-s7. The probe suggests concentrating splits inside the staircase-compatible subtree rather than uniformly.

### `rado-r5-a3-b1-frontier` — R_5(3(x-y)=1z) > 296: Li's public witness independently replayed

- Status: `open`
- Claim: [`rado/rado-r5-a3-b1-frontier/claim.json`](rado/rado-r5-a3-b1-frontier/claim.json)

**Known**

- R_5(3(x-y)=1z) > 296, from Li's public witness independently replayed by Axeyum (evidence row li-witness-296); the true value is unknown.
- R_3(3(x-y)=1z) = 27 = 3^3 (ledger claim rado-r3-a3-b1) and R_4(3(x-y)=1z) = 81 = 3^4 (ledger claim rado-r4-a3-b1, CDLW Table 10), so the law holds at k=3 and k=4 and fails at k=5.
- Lemma 4.1's lower bound R_k >= a^k remains SOUND at k=5 -- a lower bound cannot be refuted by exhibiting a larger colouring. What fails is its tightness.
- Li's public artifact repository directly supplies and verifies the 296-point witness. Axeyum independently verifies the converted artifact; the SSRN prose remains access-limited, but the lower-bound object no longer is.
- Incremental climbing from the 243 witness reached a verified 5-colouring of [251] (evidence row witness-251) and stalled at 252 across four seed families; that is a search limit, not a threshold.

**Would settle:** A verified 5-colouring of [n-1] together with an exhaustive checked refutation of F_n, for the same n. Both artifact kinds and their checkers exist in this family. The obstruction is the refutation side at five colours, which has never been done at any n for any member of this family.

**Attack notes:** The satisfiable side is not free here: the a-adic construction that settles every n <= a^k - 1 in milliseconds provably cannot reach a^k, and min-conflicts warm-started from it failed three times. What worked was cube-and-conquer, which starts from no construction at all (35.8 s). Monolithic proof-producing CDCL is the wrong tool on the satisfiable side of this instance: it emitted 2.6 GB of DRAT in 8 minutes without deciding, and its resident set tracked the proof size almost exactly, so on a 26 GiB host it would have OOM-killed before answering.

### `rado-r5-a3-b2-frontier` — R_5(3(x-y)=2z) > 358: checked five-colour frontier bound

- Status: `open`
- Claim: [`rado/rado-r5-a3-b2-frontier/claim.json`](rado/rado-r5-a3-b2-frontier/claim.json)

**Known**

- R_5(3(x-y)=2z) > 358, witnessed and verified (evidence row witness-358); the earlier 357, 350, and 319 witnesses are retained as reproducibility and historical frontier points
- The shell construction of this work yields a verified solution-free colouring of [N] with N+1 = a^k + a^(k-1) - 2a + 1; this is ATTAINED at (a,k)=(3,3) [31], (4,3) [73], (3,4) [103] and (4,4) [313], all independently re-verified, but NOT at (3,5), where it gives 318 while a 5-colouring of [319] exists. The general-k proof is asserted in the construction source and has NOT been independently verified here.
- Independent corroboration of k=5 non-tightness in a different column: Li (SSRN 6814341) reports R_5(3)>296>243 for b=1
- Canonical exact instances 351 through 357 are SAT and replayed; the 358 witness is a checked direct extension, while its paused incomplete solver proof stream has no evidentiary status; instance 359 remains open

**Would settle:** A verified 5-colouring of [n-1] together with an exhaustive cube cover refuting [n], for the same n. Both artifact kinds and their checkers exist in this family; the obstruction is the cost of refutation at k=5, not the encoding.

**Attack notes:** The satisfiable side reaches 358: exact solving produced the 357 witness, and an audited colour-4 extension plus two complete replay routes produced 358. The refutation side at five colours is still unclosed and is the real exact-value question.

## Provenance

Generated by [`scripts/gen-claims-dashboard.py`](../../scripts/gen-claims-dashboard.py) from the following committed claim files (deterministic — no timestamps, fully sorted; re-running on unchanged claims yields a byte-identical file):

- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-10/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-11/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-12/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-13/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-14/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-3-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-4-10/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-4-11/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-4-12/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-4-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-4-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-5-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-3-5-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-10/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-11/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-12/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-13/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-4/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-5/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-6/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-4-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-10/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-11/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-5/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-6/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-5-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-6-6/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-6-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-6-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-6-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-7-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-4-7-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-5-5/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-5-6/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-5-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-5-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-5-9/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-6-6/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-6-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-6-8/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-5-7-7/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-6-6-6/claim.json`
- `artifacts/claims/offdiag-schur/offdiag-schur-3-6-6-7/claim.json`
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
- `artifacts/claims/rado/rado-r4-a5-b1/claim.json`
- `artifacts/claims/rado/rado-r4-a5-b2/claim.json`
- `artifacts/claims/rado/rado-r4-a5-b3/claim.json`
- `artifacts/claims/rado/rado-r4-a5-b4-frontier/claim.json`
- `artifacts/claims/rado/rado-r4-a6-b5-frontier/claim.json`
- `artifacts/claims/rado/rado-r5-a3-b1-frontier/claim.json`
- `artifacts/claims/rado/rado-r5-a3-b2-frontier/claim.json`
- `artifacts/claims/vdw/vdw-2-3-10/claim.json`
- `artifacts/claims/vdw/vdw-2-3-11/claim.json`
- `artifacts/claims/vdw/vdw-2-3-12/claim.json`
- `artifacts/claims/vdw/vdw-2-3-3/claim.json`
- `artifacts/claims/vdw/vdw-2-3-4/claim.json`
- `artifacts/claims/vdw/vdw-2-3-5/claim.json`
- `artifacts/claims/vdw/vdw-2-3-6/claim.json`
- `artifacts/claims/vdw/vdw-2-3-7/claim.json`
- `artifacts/claims/vdw/vdw-2-3-8/claim.json`
- `artifacts/claims/vdw/vdw-2-3-9/claim.json`
- `artifacts/claims/vdw/vdw-2-4-4/claim.json`
- `artifacts/claims/vdw/vdw-2-5-5/claim.json`
- `artifacts/claims/vdw/vdw-3-3-3-3/claim.json`

Regenerate with `python3 scripts/gen-claims-dashboard.py`.
