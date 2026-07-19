# Attempt 1: final-step deletion is not a teeth control

The positive ADR-0254 route succeeds on the preregistered real query:

- exact source hash matches;
- the clean-detached exporter exits zero and reports `self_rechecked: true`;
- standard DIMACS, DRAT, and LRAT artifacts are produced; and
- pinned unchanged `drat-trim` exits zero with `s VERIFIED`.

The proof is the single line `0\n` because the exported CNF is already
refutable by unit propagation on its input clauses. Deleting the final line
therefore creates an empty proof, but `drat-trim` still reports that the input
instance itself is UNSAT and prints `s VERIFIED`. The preregistered negative
gate fails, so this attempt is rejected as a complete checker-teeth cell.

No solver, proof, or checker failure occurred. The rejection is specifically a
bad mutation design discovered only after the fixed row was exported. ADR-0255
preserves this outcome and preregisters a satisfiable-CNF substitution control
before observation.
