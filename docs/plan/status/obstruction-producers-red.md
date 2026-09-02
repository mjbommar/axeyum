# Lane: obstruction-producers-red — retire settled obstruction producers instead of erroring

<!-- plan-section: lane-status -->

**obstruction-producers-red (`IN PROGRESS`, obstruction-producers-red, 2026-09-02).**
`scripts/gen-obstruction-producers.py` is red on `main`: it dies before writing
because a hard-coded producer target was flipped to `proved`. This lane applies
the ADR-1510 policy (a contract sized against a population that has emptied must
RETIRE, not error) to the obstruction producer generator.

Reproduction, fix, mutation table and the residual policy question land here.
