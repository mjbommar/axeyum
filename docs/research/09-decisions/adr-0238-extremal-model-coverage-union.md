# ADR-0238: Extremal-model coverage-union authority control

Status: accepted
Date: 2026-07-18

## Context

ADR-0236 proves that a least-unsigned model-choice policy removes the measured
Z3/Axeyum finding divergence on a fixed 15-function tcpip prefix. It also
changes the shared finding population from 126 arbitrary-model rows to 110
least-model rows. Exact parity under one representative therefore establishes
a reproducible exploration policy, not finding preservation or coverage of the
models that policy does not choose.

The next publication gate in `PLAN.md` calls for wider fixed work or a
deterministic multi-model/coverage-union control. Before seeing the new result,
this ADR fixes a bounded two-representative experiment and its acceptance
rules.

## Decision

Add `glaurung-max-unsigned-v1` beside the accepted
`glaurung-min-unsigned-v1` policy. The maximum search is the dual of the
minimum search: it first checks path feasibility, uses temporary unsigned
lower-bound probes, rechecks the final equality, never persists a search probe,
and fails closed with the existing exhaustive reason accounting.

Define the measured **extremal coverage union** as the set union of findings
from the least-unsigned and greatest-unsigned policies. This is an opt-in
two-policy ensemble, not path forking and not enumeration of every satisfying
model.

Use Glaurung commit `e5622623ba8d8679d7e4530ff34212a5d993f030`, tcpip SHA-256
`ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`,
the first 15 of 338 reachable functions, a common 250 ms check wall, a 300,000
solve budget, a 1,800-second process wall, and three order-balanced repetitions
per policy and authority. Build separate sole-Z3 and sole-Axeyum binaries from
the same source. Run the arbitrary-model, least-unsigned, and greatest-unsigned
cells with the exact committed runner.

## Acceptance contract

Accept the bounded union only if all of the following hold:

1. The arbitrary-model control remains stable within each authority and
   reproduces ADR-0236's exact two-row Z3-only divergence and both ordered-list
   hashes. It remains a rejected parity cell.
2. The least-unsigned control reproduces ADR-0236's exact ordered-list hash.
3. Least and greatest policies each have byte-identical ordered findings under
   Z3 and Axeyum authority in all six processes.
4. Each policy has identical, repetition-stable solve counts and canonical
   attempt/probe/reason telemetry across authorities, with zero inconclusive
   choice.
5. Source, binary, input, fixed-work, timeout, environment, repetition, and
   execution-order identities match across all three cells.
6. The least/greatest set union is identical under both authorities. Every
   policy-only and arbitrary-model-only row remains explicit in the report.

Do not require the new maximum population, extremal union, or relationship to
the arbitrary-model union to have a favorable size. Those are outcomes, not
acceptance criteria. Preserve a clean negative result if any fail-closed gate
does not pass; do not change the prefix or policies in response.

## Preregistered implementation and protocol

The source series is committed as
[`glaurung-extremal-model-selection.mbox.gz`](../../../bench-results/glaurung-tcpip-extremal-coverage-union-20260718/glaurung-extremal-model-selection.mbox.gz),
SHA-256 `7916ff88bfc96b7aee6d9f1e23d73632b9712469e96c811edbf8ce970196a4a2`.
The exact orchestration is
[`scripts/run-glaurung-authority-coverage-union.sh`](../../../scripts/run-glaurung-authority-coverage-union.sh),
and the fail-closed cross-cell checker is
[`scripts/analyze-glaurung-authority-coverage-union.py`](../../../scripts/analyze-glaurung-authority-coverage-union.py).

Before the campaign, focused Glaurung minimum/maximum/parser tests pass under
both `solver-z3` and `solver-axeyum`; all 20 runner/analyzer unit tests and
shell validation pass. These engineering checks are not campaign evidence.

## Evidence

The exact committed runner completes and the fail-closed analyzer accepts the
campaign. The arbitrary-model control reproduces 128 stable Z3-authority rows,
126 stable Axeyum-authority rows, and the exact two Z3-only rows. The
least-unsigned control reproduces its 110-row ordered hash, 80,563 solves,
1,206 attempts, 1,204 completed choices, two infeasible paths, 79,466 probes,
and zero inconclusive choices under each authority and repetition.

The new greatest-unsigned policy produces 84 byte-identical ordered findings
under both authorities in all six processes. Each repetition has 34,659
solves; canonical telemetry is identical at 513 attempts, 513 completions,
33,858 probes, and zero infeasible, inconclusive, unsupported, unknown, or
error choices.

The accepted deterministic extremal union has 125 findings: 69 common to both
policies, 41 least-only, and 15 greatest-only. It is byte-identical under both
authorities. Against the arbitrary-model combined union of 128, the sets have
95 shared, 33 arbitrary-only, and 30 extremal-only rows. Thus the experiment
accepts authority parity but directly rejects any claim that these two extrema
preserve or subsume arbitrary-model findings.

The full artifact and hashes are recorded in
[`README.md`](../../../bench-results/glaurung-tcpip-extremal-coverage-union-20260718/README.md).

## Consequences

The paper may report backend-independent finding parity for this bounded
deterministic two-extremum union and the exact overlap with the rejected
arbitrary-model population. It must report the 33 arbitrary-only rows and may
not call two extrema exhaustive multi-model coverage, finding preservation, or
proof that neither solver misses a true positive. Policy-dependent process
times are not solver performance.

The default Glaurung behavior remains arbitrary model choice. Both extremal
policies remain experimental and opt in.
