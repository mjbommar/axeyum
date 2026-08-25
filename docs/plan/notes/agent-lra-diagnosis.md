# Notes: agent-lra-diagnosis

Detail moved out of [`../status/agent-lra-diagnosis.md`](../status/agent-lra-diagnosis.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Next: the shipped form of that fix is **not** the constant this A/B moved —
minimisation should be budget-driven rather than width-gated, keeping the memory
protection the `Large` bucket exists for. Nothing here has been through
`scripts/parity-run.sh`, which is still gated by nothing (gap #2).

Full finding, all counts and controls:
[`../../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md`](../../research/05-algorithms/linear-arithmetic-deficit-diagnosis-2026-08-21.md).
