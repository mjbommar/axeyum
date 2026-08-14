# Lane: agent-h — clausal proof reconstruction

<!-- plan-section: lane-status -->

**Clausal reconstruction lane (`DONE`, agent-h, 2026-08-13).** `DP_POOL_BUDGET`
is not the ceiling; LRAT hint chains bypass that fallback. Compact reconstruction
(`1b2b13c70`) is smaller/faster, scales linearly with hint count, reconstructs
two four-colour cases the inlined route cannot, and introduces no statement or
axiom-footprint mismatch. Nineteen refutations check in Lean 4.30. **Next:**
kernel arena checkpointing, spooling admitted theorems before truncation so
proof size becomes disk-bounded rather than RAM-bounded.
