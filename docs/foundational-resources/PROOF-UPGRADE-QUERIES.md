# Proof Upgrade Queries

This is the consumer-facing query guide for the proof-upgrade queue. It
complements the hand-authored
[Proof Upgrade Frontier](PROOF-UPGRADE-FRONTIER.md), the compact
[Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md), the
[Proof Route Query Matrix](PROOF-ROUTE-QUERY-MATRIX.md), and the learner-facing
[Proof Route Learner Snippets](../learn/math/proof-route-learner-snippets.md).

Use this guide when a proof contributor wants to find rows that are still
finite replay, compare them with already checked rows, and decide whether a new
certificate would teach a genuinely new proof shape.

## Boundary

`replay-only` is not a defect. Many rows should stay replay-only because the
finite model checker is the right trusted core for that claim.

Promote a row only when the certificate adds something the replay row does not:

- a Boolean CNF/LRAT proof object for a finite Boolean refutation;
- a QF_BV bit-blast proof where fixed width is part of the claim;
- a QF_LIA/Diophantine certificate for an integer obstruction;
- a QF_LRA/Farkas certificate for exact rational infeasibility;
- a QF_UF/Alethe certificate for an equality or congruence conflict;
- a Lean route for a general theorem that is outside finite replay.

Do not use these queries to turn bounded examples into theorem, benchmark, or
parity claims.

## Start Here

Summarize the active proof families:

```sh
python3 scripts/query-foundational-resources.py routes \
  --route boolean \
  --require-any

python3 scripts/query-foundational-resources.py routes \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py routes \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py routes \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py routes \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py routes \
  --route lean \
  --require-any
```

These route summaries count packs, checks, proof statuses, result statuses,
fields, and sample packs. Use them before choosing another proof-upgrade
increment.

## Replay-Only Row Discovery

Find all replay-only UNSAT rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status replay-only \
  --expected-result unsat \
  --require-any
```

Field-scoped replay queues:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field probability_theory \
  --proof-status replay-only \
  --expected-result unsat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field abstract_algebra \
  --proof-status replay-only \
  --expected-result unsat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --field topology \
  --proof-status replay-only \
  --expected-result unsat \
  --require-any
```

SAT witnesses can stay replay-only indefinitely. Query them separately when the
goal is witness coverage rather than certificate promotion:

```sh
python3 scripts/query-foundational-resources.py checks \
  --field graph_theory \
  --proof-status replay-only \
  --expected-result sat \
  --require-any
```

## Route-Relevant Packs With Replay Rows

Use pack-level filters to find families that contain replay rows and already
advertise a proof route. This is often better than row-level route filtering,
because replay rows may not carry the route string after a separate checked
proof row has been split out.

```sh
python3 scripts/query-foundational-resources.py packs \
  --proof-status replay-only \
  --route Farkas \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --proof-status replay-only \
  --route Alethe \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --proof-status replay-only \
  --route Diophantine \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --proof-status replay-only \
  --route qf-bv \
  --require-any

python3 scripts/query-foundational-resources.py packs \
  --proof-status replay-only \
  --route boolean \
  --require-any
```

Pick from these pack lists only after checking
[Proof Route Family Selection](PROOF-ROUTE-FAMILY-SELECTION.md). The rule is:
do not add another checked row unless it teaches a new proof shape, trust
boundary, solver pressure, or downstream query shape.

## Checked Evidence Contrast

Use checked-row queries to compare a proposed promotion with existing coverage:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status checked \
  --expected-result unsat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --route Farkas \
  --proof-status checked \
  --expected-result unsat \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --route Alethe \
  --proof-status checked \
  --expected-result unsat \
  --require-any
```

If an existing checked row already teaches the same certificate shape, keep the
new source row as replay-only and improve learner text instead.

## Horizon Rows

For general theorem boundaries, use
[Theorem Horizon Queries](THEOREM-HORIZON-QUERIES.md). Horizon rows are proof
targets, not replay rows and not checked SMT evidence:

```sh
python3 scripts/query-foundational-resources.py checks \
  --proof-status lean-horizon \
  --require-any
```

## Promotion Checklist

Before landing a proof upgrade:

- identify the exact finite object and source replay row;
- state why replay alone is not the most useful trust story;
- link the relevant proof-cookbook recipe;
- add the route-specific artifact or regression;
- validate the affected pack;
- run `./scripts/check-foundational-resources.sh`;
- keep theorem-horizon and benchmark claims out of the proof-upgrade commit.

The output should preserve the same identity throughout: untrusted fast search,
trusted small checking.
