# Glaurung external DRAT consumption — 2026-07-19

Status: accepted external interoperability plus v2 checker sanity control; v1
final-step-deletion design retained as rejected

ADR-0254 selected the lowest-hash UNSAT in the fixed 1,024-query holdout before
standard proof export. Axeyum emitted a self-rechecked DIMACS/DRAT/LRAT bundle,
and pinned upstream `drat-trim` independently printed `s VERIFIED`.

The preregistered negative control deleted the final DRAT line. This query's
CNF is already UNSAT by input unit propagation and the complete DRAT is only
the empty-clause line `0\n`. Consequently, `drat-trim` also verified the input
with an empty proof. The overall ADR-0254 cell is rejected because the negative
gate lacks teeth; the positive result remains valid interoperability evidence
but is not promoted alone as an accepted cell.

[`attempt-1-final-step-deletion-rejection/`](attempt-1-final-step-deletion-rejection/)
records exact identities, hashes, sizes, checker streams, and claim limits. The
access-controlled query and derived CNF/DRAT/LRAT bytes are not committed.

ADR-0255 preregistered a corrected teeth control before running it: replace only
the input with the exact satisfiable DIMACS text `p cnf 1 0\n`, keep the same
two-byte proof, and require the checker not to report `s VERIFIED`.

[`accepted-v2-satisfiable-cnf-control/`](accepted-v2-satisfiable-cnf-control/)
records the accepted result: the unchanged real pair verifies, while the same
proof against the exact satisfiable control exits 1 with `s NOT VERIFIED`.
ADR-0256 accepts this bounded interoperability/checker-sanity cell while keeping
the trivial-proof limitation explicit.

[`nontrivial-scan-no-selection/`](nontrivial-scan-no-selection/) records
ADR-0257's fixed-cap follow-on. All 32 hash-ordered exports succeed, but every
DRAT is again the same two-byte empty-clause proof; ADR-0258 retains the
preregistered `no-selection` and closes further mining of this holdout.
