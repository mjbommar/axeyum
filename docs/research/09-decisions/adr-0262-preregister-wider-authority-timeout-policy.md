# ADR-0262: Preregister wider authority timeout/policy evidence

Status: proposed
Date: 2026-07-19

Result state: preregistered; no driver cell observed

## Context

ADR-0233 already closes the neutral timeout-sensitive **formula** control: 52
exact tcpip formulas were swept at 50/100/250/1000 ms across Axeyum, Z3, and
cvc5 with complete decision-population accounting. The remaining reviewer gap
is end-to-end sole-authority **finding** sensitivity, where model choice and
per-check nondecisions can change concretization, exploration, and emitted
findings.

ADR-0236 measures the first 15 of 338 reachable tcpip functions at 250 ms.
AnyModel produces a stable two-row raw authority difference; LeastUnsigned
restores exact raw parity at substantially greater work. ADR-0247 later sweeps
all five executable scalar settings on that same prefix, but tcpip remains a
zero-high-confidence, unlabeled diagnostic population. ADR-0250 then proves
that an outer function count alone is insufficient: a fixed prefix can conceal
an inner wall-deadline stop. Future fixed-work authority evidence must use the
v6 stop partition exposed by isolated Glaurung `ff3c0a7`.

The next experiment must therefore widen the actual explored prefix, separate
timeout cells, retain the arbitrary-model control beside the canonical setting,
and fail closed on hidden inner work. It is a sensitivity/faithfulness result,
not a real-world recall denominator or speed benchmark.

## Decision

Run exactly six tcpip sole-authority cells:

```text
{AnyModel, LeastUnsigned} x {100 ms, 250 ms, 1000 ms}
```

Each cell uses three order-balanced repetitions of independently compiled
Z3-only and Axeyum-only `ioctlance` binaries, for six processes per cell and 36
processes total. Analyze exactly the first 20 of 338 reachable functions. This
is wider than every accepted tcpip authority/policy cell while remaining below
ADR-0236's abandoned 30-function/200,000-solve boundary.

Use these fixed controls in every process:

- Glaurung revision `ff3c0a767a0b085f8552bdb2b363c0b7fa273cbe`;
- tcpip SHA-256
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`;
- outer function limit 20, solve budget 400,000, per-worklist time safety cap
  900 seconds, driver deadline 2,400 seconds, and process cap 2,700 seconds;
- explicit per-check wall timeout equal to the cell's 100/250/1000 ms value;
- raw output plus the versioned high-confidence partition; and
- ADR-0250's required v6 worklist-stop partition.

AnyModel is the unselected default A0 policy. LeastUnsigned is selected through
`GLAURUNG_CONCRETIZATION_POLICY=min-unsigned`; the legacy selector is not used.
Do not add Maximum, site-hash, BoundarySet, DiverseEnum, or symbolic memory to
this matrix. The five-scalar prefix-15 sweep is already complete; this protocol
asks whether the cheapest canonical control remains feasible and parity-
producing when both width and timeout change.

## Validity and interpretation gates

Every cell must:

- use schema v6, exact clean source/input/binary identities, and the declared
  environment;
- complete all six processes with stable within-backend work and findings;
- analyze exactly 20/338 functions at the declared fixed-work boundary;
- report one internally consistent worklist-stop partition per process, with
  zero `timeout_budget` and zero `deadline` stops and stable per-backend
  partitions;
- exercise the expected policy identity with zero inconclusive model choices;
  and
- preserve exact high-confidence authority parity.

High-confidence parity is the protocol validity gate because the corrected
tcpip population has no independently validated positive rows. Raw parity is a
reported hypothesis, not a validity condition. The analyzer separately reports:

- raw Z3-only/Axeyum-only counts for every cell;
- whether AnyModel has raw parity at all three timeouts;
- whether LeastUnsigned has raw parity at all three timeouts; and
- per-authority finding counts, solve counts, elapsed time, RSS, policy work,
  and inner-stop partitions.

A raw difference is an admissible result. A missing/rejected cell, source or
binary drift, hidden deadline/timeout stop, unstable population, high-confidence
difference, or inconclusive policy choice rejects the campaign. Preserve every
failed cell and do not change the prefix, timeout list, policy list, budgets,
repetition count, or acceptance population in response. A revised experiment
requires a new ADR.

Wall time remains the swept independent variable and safety mechanism here;
this protocol does not call its cells deterministic. A1's separate
backend-specific `resource_limit`/Z3 `rlimit` configuration remains future
wiring, and their numerical units must not be treated as cross-backend work
equivalents.

## Preregistration evidence

The authority binaries were compiled from clean Glaurung `ff3c0a7` against
Axeyum `68c6245c` before any driver execution:

- Z3-only SHA-256:
  `63863636b1cd064c664c593b15a29f9e5ab791b013dbf925666481df1861772a`;
- Axeyum-only SHA-256:
  `f4f9312fb0257b0a8f4e2a6422247b7dfc279c1a9b308177fa1b9fda2f1c57a5`.

The build emitted only inherited Glaurung warnings. No authority binary was run
on tcpip while defining the protocol.

`scripts/analyze-glaurung-authority-timeout-policy.py` validates the complete
matrix independently of producer acceptance. Its tests began red because the
analyzer did not exist. Five focused tests now cover a valid matrix with a raw
AnyModel difference, a missing cell, legacy-schema rejection, hidden timeout-
stop rejection, and source drift. Together with the 26 existing authority-
producer tests, all 31 pass. The shell runner passes `bash -n`; the analyzer
passes Python bytecode compilation.

## Alternatives

- Repeat the 15-function/250 ms canonical result: rejected because it adds no
  width or timeout evidence.
- Sweep only AnyModel: rejected because backend-dependent value choice would
  remain inseparable from timeout sensitivity.
- Run all five scalar settings: rejected because ADR-0247 already measures that
  knob and the site-hash cells are materially expensive; LeastUnsigned is the
  accepted minimal canonical control.
- Use a single 250 ms wider cell: rejected because the reviewer explicitly asks
  for timeout sensitivity and ADR-0233 shows decision populations change across
  the frontier.
- Treat equal outer function counts as fixed work: rejected by ADR-0249/0250's
  observed hidden inner deadline.
- Gate on raw `>= AnyModel` or on raw equality: rejected because every current
  tcpip row is diagnostic and unlabeled; neither raw cardinality nor producer
  confidence is ground truth.

## Consequences

ADR-0262 is the next publication-evidence action and supersedes stale plan text
requesting more neutral timeout formula breadth. It does not reopen A0, create a
new concretization algorithm, admit BoundarySet/DiverseEnum successor mechanics,
or justify symbolic memory. A2 remains gated on a genuinely broader labeled
residual gap.

If the exact matrix is valid, it characterizes whether the first canonical
policy remains raw-authority-parity-producing over a wider prefix and across
explicit timeout cells. If it rejects, the preserved failure identifies the
resource or reproducibility boundary without being tuned away. Either result is
reported separately from ADR-0233's neutral formula timing and from performance
headlines.
