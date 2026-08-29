# 249 — IVT row 2 as a kernel theorem

Status: IN PROGRESS (first commit, work not yet landed — this file is a stub so
the lane's work is visible on the branch before any long check runs).

Task: land IVT's ADR-0603 row 2 (the boundary/unprovability witness) as a
kernel declaration, on the model of `CReal.evt_attained_max_decides_sign`.

Findings so far:
- Confirmed the gap is real at the merge base: no `ivt_*decides*` declaration.
- `CReal.max`, `CReal.min`, `CReal.abs` all exist; there is NO
  `uniformly_continuous_abs` / `_max` / `_min`, so the plateau family's
  hypothesis-class bridge is the expensive half.
