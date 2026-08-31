# Lane: unblock-draw-15

Status: IN PROGRESS — searching for a cycle-index-3 family for draw 15.

Context: ADR-1095 / ADR-1100 / ADR-1115. Four consecutive honest declines.
The constraint is positional: `assign_partitions` assigns held-out at cycle
indices 0 and 3, and index 3 needs a late-sorting, topically fresh,
R9/R11/R12-clean family. ADR-1115 widened `is_closed_evaluation` to see
ground predicates, so a candidate's pool can now be screened for
reduction-settled rows BEFORE any definition is declared.

## Landed changes

(pending)
