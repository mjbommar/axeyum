# 323 — mobility census: the gate fails because we succeeded

<!-- plan-section: lane-status -->

Status: IN PROGRESS (initial commit, investigation only — no fix yet).

`python3 scripts/check-mobility-census.py` exits 1 with 126 violations, all one
sentence: `F:<id> is proved in the ledger; the census is over OPEN facts`. The
census is a snapshot measurement; facts closing after it was taken is the
flywheel working, not a defect in the artifact.

Investigation in progress. Nothing changed yet.
