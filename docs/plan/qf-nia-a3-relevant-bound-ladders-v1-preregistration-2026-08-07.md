# QF_NIA A3 relevance-activated bound ladders v1 preregistration — 2026-08-07

## Selection boundary

Baseline is clean integrated
`a28560f81db34248413f27382b706ab7c5b9b60f`. The complete QF_NIA causal
population remains bound by census SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a`
and retained-sidecar SHA-256
`392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524`.

The exact ordered target list is
[`relevant-bound-ladders-v1-targets.txt`](evidence/qf-nia-a3/relevant-bound-ladders-v1-targets.txt),
SHA-256
`f781c5d8dcc550d2187571afbd8fe3676fbaf0dddaeaac1cee0767dc9448b6ac`:

- `juHashMapCreate...p4943`;
- `juHashMapCreateContainsValue...p32598`.

The current release `explain_corpus` binary has SHA-256
`b4c55749c5cfd25c89422f3e3251cd083563d84d2cac6ab30c3c7aeed78ad77e`.
Fresh serialized direct observations under 8 GiB and 24,000 ms show:

| Target | Atoms | Lazy rounds | Initial bound lemmas | Dynamic core sources |
|---|---:|---:|---:|---|
| `p4943` | 6,368 | 82 | 390 | 197 simple-bound, 72 LP; length 2–30 |
| `p32598` | 9,584 | 22 | 126 | 237 simple-bound, 14 LP; every core length 2 |

Both targets reach the same actionable path in the current observation: every
lazy round finds a support conflict, neither attempts model reconstruction nor
falls back to the full arbitrary assignment, and most learned clauses are
already-checkable two-literal simple-bound conflicts.

## Causal hypothesis

The arithmetic DPLL already knows adjacent monotonicity implications for
simple integer-bound ladders. For example, `x >= 2` implies `x >= 1`, and the
same rule applies to complement literals. These are sound two-literal theory
lemmas checked by the existing arithmetic-lemma verifier.

Today the complete implication pass is disabled when an abstraction exceeds
512 atoms. That correctly avoided broadly inserting thousands of irrelevant
clauses on earlier UFLIA workloads, but the two selected rows are respectively
6,368 and 9,584 atoms and then rediscover related bound conflicts in every
round. The hypothesis is that relevance activation can expose the existing
checked implications only for an expression that has produced a real dynamic
simple-bound conflict, avoiding both broad pre-seeding and another exact-theory
oracle call.

## Authorized mechanism

This preregistration authorizes one implementation experiment:

1. Preserve the existing complete implication behavior for abstractions of at
   most 512 atoms byte-for-byte.
2. For larger abstractions, construct a deterministic latent index of adjacent
   simple-bound implications, grouped by stable expression term ID and bound
   side. Constructing the index adds no SAT clause and invokes no theory
   oracle.
3. After the existing integer oracle proves the current support inconsistent
   and the existing cheap extractor returns a `Bound` conflict, activate the
   latent lower/upper ladders for the expression or expressions named by that
   conflict.
4. Activate each expression at most once. Visit expression IDs, bound sides,
   thresholds, atom IDs, and truth polarities in stable sorted order.
5. Add only adjacent implications and retain the existing global maximum of
   4,096 implication lemmas per arithmetic-DPLL instance. Do not raise the
   batch limit, atom limit, round limit, node limit, deadline, or any encoding
   ceiling.
6. Record every activated implication as the same two-literal
   `ArithLemmaLiteral` core used by certification. Do not accept a SAT result
   without selected-literal and original-assertion replay.

The additional theory-oracle work bound is exactly zero calls. Index
construction is linearithmic in the existing atom population; activated clause
construction is bounded by 4,096 two-literal clauses and stops permanently at
that existing ceiling. There is no elapsed-time policy, randomness, path or
basename match, adaptive cap, or second activation pass.

Environment-gated counters may report latent expressions/implications,
activated expressions/implications, and whether the 4,096 ceiling was reached.
They must not record source terms, models, literal identities, or timings, and
must not affect policy.

## Controls

The exact ordered routing-control list is
[`relevant-bound-ladders-v1-routing-controls.txt`](evidence/qf-nia-a3/relevant-bound-ladders-v1-routing-controls.txt),
SHA-256
`f45ea298df3a64d82130c99e67af414379b4686d3a6f53178975402977c25edd`:

- load-sensitive `p1784`, which shifted to reconstruction deadline in the
  current direct observation;
- `SAT14/1051` and `SAT14/1280`, whose broad-core group-deletion mechanism is
  closed negatively and must not be revived by this work.

Mandatory semantic controls are the six reference-UNSAT rows in
`reconstruction-deadline-v1-controls.txt` (SHA-256
`cf8d03e83b237aeea2413bf23b317b590429c40f08e0d955e8b50824212014e3`),
all 34 retained QF_NIA decisions, the ADR-0378 giant-`distinct` survival row,
and existing small-core, upfront implication, certification, model-replay,
typed-decline, and opaque-UF tests.

## Gates and stop conditions

1. Add unit tests proving one conflict activates one expression once, emitted
   implications are adjacent and certified, unrelated ladders stay latent, and
   the 4,096 ceiling is deterministic.
2. Run each target three times under the unchanged 8 GiB / 24,000 ms protocol.
   At least one target must become replay-checked SAT in at least two of three
   runs before control or whole-list expansion.
3. If the target gate passes, run the three routing controls, six UNSAT
   controls, and exact 34-decision retained set. Every prior decision must be
   identical and every new SAT model must replay.
4. A fresh 200-row QF_NIA measurement is authorized only after all earlier
   gates pass. The implementation is retainable only for a monotone result with
   zero disagreements and no memory or deadline breach.

Reject and remove the implementation if neither target gains, a SAT replay
fails, a reference-UNSAT row becomes SAT, any retained decision is lost, the
4,096 ceiling is exceeded, memory crosses 8 GiB, or an unrelated ladder is
activated. Do not compensate by raising a cap, reserving fresh time, changing
route order, adding full-theory probes, or making behavior fixture-specific.
