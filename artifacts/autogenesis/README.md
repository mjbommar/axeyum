# Autogenesis operation registry

`operations.json` is the reviewed mapping from a fact shape to typed producer,
checker, and admission operations. It contains identifiers and implementation
paths, never caller-authored shell commands.

The first operation is deliberately `counterfactual-fixture-only`. It records
the Nat induction path exercised by the Autogenesis-1 control, but grants no
authority to dispatch or admit an authoritative ledger fact. Run
`python3 scripts/validate-autogenesis-operations.py` after changing it.

`nursery-v1.json` is the leakage-controlled population manifest introduced by
ADR-0478. Its first two entries remain the frozen Autogenesis-1 longitudinal
regression; they never count toward train, development, held-out, or autonomous
yield. The additional 214 entries are frozen by
`mathlib-nursery-split-policy-v1.json` and regenerated with:

```sh
python3 scripts/create-autogenesis-mathlib-nursery-split.py --check
python3 scripts/check-autogenesis-nursery.py --require-ready
```

The split policy fixes family membership before target outcomes, and the checker
rejects dependency-component, source-review-group, family, family-scoped
proof-shape, mutation, or longitudinal leakage. Route hypotheses grant no
dispatch or admission authority.

`mathlib-nursery-dispatch-baseline-v1.json` is the first post-freeze capability
census. It inspects only train and development contracts, never held-out facts,
proof bodies, or target outcomes. Reproduce it with:

```sh
python3 scripts/create-autogenesis-nursery-dispatch-baseline.py --check
```

A row declined before execution is not a proof attempt and consumes zero
producer budget. The distinction prevents missing adapters from being reported
as solver failures.

`mathlib-statement-adapter-v1.json` binds the first proof-isolated surface-to-
kernel goal. Its target proposition is encoded as a transparent `Prop`
definition, never an axiom or theorem. The checker rehashes the immutable
external export, independently imports it, rejects any trusted/proof-bearing
declaration, and pins the resulting goal identity:

```sh
python3 scripts/check-autogenesis-statement-adapter.py
```

`mathlib-statement-reflexivity-v1.json` binds the immutable pre-admission
identity of the first proof candidate built
from that checked goal. The untrusted proposer recognizes only a bounded Pi
telescope ending in exact equality; the independent kernel, dependency audit,
and receipt checker decide whether its `Eq.refl` term is acceptable. The
artifact deliberately records zero ledger writes. The exact authoritative
operation is registered separately in `operations.json`; any later fact credit
must bind this unchanged manifest through the durable transaction protocol:

```sh
python3 scripts/check-autogenesis-statement-reflexivity.py
```

`mathlib-statement-reflexivity-admission-v1.json` binds the first ordinary
open-to-proved ledger transition produced from that candidate. Its external
bundle retains both frontiers, the clean-commit execution, prepared transaction,
crash-recovery journal, durable event, readiness delta, before/after facts, and
a complete Git bundle. It also binds the separately retained raw objects from
an isolated clean-worktree semantic replay. Unlike the pre-admission checker,
this result checker requires both external bundles, validates their complete
file indexes and content-addressed chains, and replays the settled operation:

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py
```

`mathlib-reflexivity-coverage-v1.json` binds the first sealed bottom-up
train/development census. Each of 138 mapped definitions has an isolated
proof-free export, so one contaminated dependency closure cannot hide another
row's adapter or kernel outcome. The external archive also retains the rejected
combined-stream probe and two byte-identical observations. This is diagnostic
evidence with zero ledger writes:

```sh
python3 scripts/check-autogenesis-reflexivity-coverage.py
```

`mathlib-factorial-zero-family-v1.json` binds the first reusable proof-free
adapter family. Both frozen train propositions are exported from one source and
checked in isolated fresh kernels, while each authoritative registry row stays
exact to one fact and immutable stream. The checker requires the external
objects and rejects held-out access, proof-body access, family expansion, or a
shared authority shortcut:

```sh
python3 scripts/check-autogenesis-factorial-zero-family.py
```

`mathlib-checked-type-slice-replay-v1.json` binds the first semantic
train/development type-slice census. Its 128 accepted receipts each identify
the exact source stream, generalized goal, abstractions, retained environment,
fresh-kernel target, and successful exact specialization. Ten rows remain
typed declines; no proof producer ran and no ledger credit changed. Bulk
receipts remain in the immutable external observation:

```sh
python3 scripts/check-autogenesis-checked-type-slice-replay.py
```

`mathlib-auto-param-binder-replay-v1.json` binds the separately versioned
extension that closes the ten typed declines without changing the historical
route. It requires 128 exact v1 receipts and ten v2 receipts whose normalized
constructor/recursor identities, dependency identities, source `autoParam`
identity, and rewrite counts match the immutable observation. All 138 rows are
proof-free goal boundaries; no source theorem or ledger transition is claimed:

```sh
python3 scripts/check-autogenesis-auto-param-binder-replay.py
```

`mathlib-type-slice-producer-census-v1.json` binds the first fixed-budget
producer run across all 138 checked train/development slices. The checker
requires one valid slice receipt and one structured proof outcome per row,
recomputes the source and observation identities, pins the two accepted proof
identities and their zero-dependency audits, and rejects budget, outcome,
receipt, proof, authority, or mutability drift. It grants no operation or
ledger authority:

```sh
python3 scripts/check-autogenesis-type-slice-producer-census.py
```

`producer-outcome-observations-v1.json` is a generated, outcome-safe view of
that same pinned census, grouped by reviewed fact family, statement shape, and
exact-source versus semantic-abstraction boundary. It contains train/development
rows only, explicitly records zero held-out observations, and grants no
operation, proof, admission, or scheduling authority:

```sh
just autogenesis-producer-outcomes
```

`producer-evaluation-frontier-v1.json` is the deterministic, partition-safe
input set for a future general-producer run. It selects dependency-ready facts
only from the frozen train/development partitions and reports held-out or
out-of-population ready facts only as aggregate exclusions:

```sh
just autogenesis-producer-evaluation-frontier
```

`mathlib-factorial-zero-admission-v1.json` binds the second family member's
clean-commit execution, crash-recovered ledger transition, complete external
archive, and detached-worktree replay. It uses the same generic admission
verifier as the first member but supplies its own canonical result manifest:

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py \
  --manifest artifacts/autogenesis/mathlib-factorial-zero-admission-v1.json
```

`mathlib-statement-source-v1.json` binds the external statement-only Mathlib
v4.30.0 inventory. Bulk NDJSON stays on `/nas3`; Git retains the extractor,
source identity, selection policy, and small derived candidate view. Neither an
imported theorem nor its source name counts as Axeyum proof construction.

```sh
python3 scripts/check-autogenesis-mathlib-source.py
python3 scripts/create-autogenesis-mathlib-candidates.py --check
python3 scripts/create-autogenesis-mathlib-dependency-components.py --check
```

`mathlib-dependency-source-v1.json` binds a second, evaluation-only external
artifact. Its extractor can inspect upstream theorem values, but emits only
names and direct theorem dependencies. The committed component projection
contains only candidate identities, candidate-to-candidate edges, and whole
weak components. It is split input, not proposer input, and it still assigns no
train, development, or held-out membership.

`mathlib-nursery-review-policy-v1.json` is the outcome-blind human review
authority. Its derived artifact removes aliases and internal helper surfaces,
reserves base cases for calibration, and binds one statement-strength mutation
to each of the twelve families. The resulting 120 groups still have no split:

```sh
python3 scripts/create-autogenesis-mathlib-nursery-review.py --check
```

`mathlib-nat-int-fact-catalog-v1.json` maps the 202 reviewed sources and twelve
mutations to 214 ordinary **open** fact-ledger rows. Source declarations remain
external prior art; mutation truth values remain unknown. Their
`lean4-surface` propositions were accepted as proof-free axiom types by the
exact Mathlib v4.30 environment, which checks syntax and typing but proves
nothing:

```sh
python3 scripts/create-autogenesis-mathlib-fact-catalog.py --check
```
