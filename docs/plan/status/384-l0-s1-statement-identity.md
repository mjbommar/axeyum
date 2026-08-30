# L0/S1 — Bind statement identity

<!-- plan-section: lane-status -->

Lane: `l0-s1-statement-identity`
Phase: S1 of the trusted-library safety roadmap (ADR-0717, selected by ADR-0746)
Status: IN PROGRESS — early commit, work incomplete.

## The gap S0 measured

`artifacts/safety-matrix/safety-matrix.tsv`: `exact_statement` 142 / 2117.
Measured in this lane against the ledger directly:

| population | settled | pinned |
|---|---:|---:|
| all settled facts | 2120 | 144 |
| `F:ml430-*` mirrors | 375 | 27 |
| native (non-mirror) | 1745 | 117 |

Mirrors have a second, stronger guard — `check-mirror-statement-fidelity.py`
hashes `formal.statement` against a preregistered catalog. Native facts have
no equivalent, and `check-settled-fact-statements.py` treats absence from the
pin manifest as "newly settled", never as a gap.

## Work in progress

Not yet landed. This file is committed early so the lane's findings survive
an interruption.
