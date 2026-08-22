# Production measurement and the general producer

Date: 2026-08-22
Status: proposed — not yet entered in the live queue
Supersedes nothing; **re-asserts the sequence already set by**
[`16-mathlib-frozen-nursery-split-result.md`](16-mathlib-frozen-nursery-split-result.md)
and [`17-mathlib-nursery-dispatch-baseline.md`](17-mathlib-nursery-dispatch-baseline.md)

## Thesis

The flywheel's limiting arrow is the **producer**, not the solver and not the
checker. The goal queue is full, the admission machinery works, and the trusted
base is defended — but every registered operation names exactly one theorem, and
every theorem it names was already proved. We have been hand-impersonating the
missing producer and recording the results through autogenesis plumbing, which
makes the programme's headline claim unfalsifiable in both directions.

Before any of that can be fixed, one thing must be contained: **the held-out
evaluation partition has been breached.**

## What is measured

Every number below is read from a committed artifact, not from a doc or a label.
Reproduction commands are in the last section.

### The operation registry is a fact-ID dispatch table

```text
operations registered in artifacts/autogenesis/operations.json      24
  ...whose applicability names more than one fact                    0
distinct fact_ids covered by all 24 operations                      23
  ...of those, still open                                            0
dependency-ready open facts                                        144
  ...with a registered applicable operation                          0
positive control — covered facts that ARE settled                   23
```

Every operation carries `applicability.fact_ids`, an enumerated list. Not one
names more than a single fact. Even `authoritative-mathlib-statement-reflexivity-v1`
— whose producer, `bounded-pi-equality-reflexivity-v1`, is plainly a general
capability — is pinned to one ID.

Registry coverage is therefore **23-of-23 on the past and 0-of-144 on the
future**. That is not a producer with a low conversion rate; it is a per-target
dispatch table wearing the admission machinery.

This is the repository's own signature failure moved one arrow upstream. A
checker that cannot fail is worse than no checker. **An operation registry that
only ever names theorems someone already proved cannot fail to "produce", and
cannot produce anything new.**

### The held-out partition has been breached

[`16-…-frozen-nursery-split-result.md`](16-mathlib-frozen-nursery-split-result.md)
preregistered 214 propositions as train 78 / development 60 / held-out 76, with
`<family>:<statement-shape>` as the split key **specifically because whole
families share proof templates**. The README's programme guarantees include
"every policy improvement is evaluated against immutable held-out populations."

Measured 2026-08-22:

| Fact | `F:ml430-nat-gcd-greatest-0a04214a` |
|---|---|
| Partition (frozen manifest) | **`held-out`** |
| Family / proof shape | `natural-gcd` / `natural-gcd:conditional-proposition` |
| Status | `proved`, route `kernel-lean` |
| Operation naming it | `authoritative-mathlib-nat-gcd-greatest-kernel-capsule-v1` |
| Registered | **2026-08-21**, commit `6e112b4bc` |

Because the family is the declared unit of contamination, the blast radius is
the family, not the row: **`natural-gcd` is 19 of 76 held-out propositions —
25% of the held-out partition.**

No gate could have caught this. `scripts/check-autogenesis-nursery.py` validates
the *manifest's internal integrity* (no family, shape, component or source group
crosses partitions) and never inspects what operations do to it.
`scripts/validate-autogenesis-operations.py` mentions `partition`, `nursery` and
`held-out` **zero times**. The immutability guarantee was prose.

### The "138 ready facts" number is a trap

Dependency-ready open `ml430` facts number 138 — numerically identical to
train + development (78 + 60). **They are not the same set:**

```text
ml430 READY (open, deps settled) = 138
  by partition:  train 44 · development 44 · held-out 50
```

Pointing a producer at "the 138 ready facts" would contaminate **50 more
held-out rows**. This plan was one sentence away from proposing exactly that.

### Production rate is currently unmeasurable

[`../formalized-math-2026-08/05-throughput.md`](../formalized-math-2026-08/05-throughput.md)
concluded on 2026-08-19 that no tool counts theorems across preludes, so the
rate is "not falsifiable in either direction." Still true on 2026-08-22:
`nat_theorem_inventory` and `int_theorem_inventory` are per-prelude, and `rat`,
`creal`, `complex`, `logic` and `string` have no theorem counter at all. Only
the **axiom** ledger is cross-prelude.

Realized rate over the only multi-day window: **6.4 theorems/day/lane against
149 projected**, `f ≈ 0.043`.

## The programme already specified this sequence

This plan invents little. Doc 16's "What comes next" reads:

> The next action is not to import Mathlib answers or hand-author proof plans.
> Run fixed-budget, outcome-recording episodes over train and development while
> keeping held-out untouched. Aggregate typed declines by family, statement
> shape, missing kernel primitive, and missing reconstruction seam. The first
> capability acquisition should be chosen from that measured bottleneck, then
> evaluated against the still-frozen held-out partition.

Doc 17 reinforces it: building search or retrieval before the narrow bridge
"would produce machinery with no legitimate input path from the nursery," and
the statement adapter is called out as the reusable capability that unlocks all
eight train/development families.

What happened between 2026-08-18 and 2026-08-22 was the opposite: **19 further
single-target capsules**, one of them into held-out. The plan was right; it was
not followed, and nothing in the gates required it to be.

## Phases

Each phase must enter the live queue through an owned file in
[`../plan/status/`](../plan/status/README.md) before implementation.

### P0 — Contain the breach (small; blocking) — **DONE 2026-08-22**

Result: [`227-held-out-partition-breach-result.md`](227-held-out-partition-breach-result.md).
Decision: [ADR-0542](../research/09-decisions/adr-0542-held-out-partition-breach-repair.md).
`natural-gcd` moved to development as a whole family; held-out re-froze at 57 rows
across three families; `scripts/check-autogenesis-holdout-isolation.py` gates both
directions and is mutation-verified. Train + development is now **157**, and the
programme's own census reports `eligible-for-dispatch 0` on the repaired population.


Nothing downstream is trustworthy until the evaluation population's identity is
repaired and made enforceable.

| Task | Path | Exit criterion |
|---|---|---|
| P0.1 Record the incident | this doc + a result doc | The breach is stated with fact id, operation id, commit, date, and blast radius. Not deleted, not quietly rewritten. |
| P0.2 Reclassify `natural-gcd` | `artifacts/autogenesis/nursery-v1.json` + policy | The family moves out of held-out **as a whole**, or held-out is re-frozen at 57 rows with the exclusion recorded by name. Whichever is chosen, the manifest states the partition was amended, when, and why. |
| P0.3 Gate it | `scripts/validate-autogenesis-operations.py` | An operation whose `applicability.fact_ids` names a held-out fact is a **hard failure**. Mutation-verified: delete the guard, exactly one test dies. |
| P0.4 Negative control | `scripts/tests/` | A fixture operation naming a held-out fact must fail the gate, and an otherwise identical one naming a train fact must pass. Without the second half the gate could be a constant. |

**Do not** re-run any producer over held-out to "check whether it mattered."
Measuring the contaminated partition is what destroys it.

### P1 — Fail-closed cross-prelude production counter — **DONE 2026-08-22**

Two generated ledgers, both gated in `just check` and `scripts/check.sh`:

- [`theorem-production-ledger.md`](../plan/generated/theorem-production-ledger.md) —
  **418 distinct theorems, all axiom-free**, across all eight preludes. The
  throughput strand's "nobody can measure this" finding is closed.
- [`production-provenance-ledger.md`](../plan/generated/production-provenance-ledger.md) —
  of 136 established facts, **0 via an operation covering more than one fact**,
  21 via single-target capsules, 115 hand-constructed or imported.


The precondition for every later phase: right now no producer work can be shown
to have helped or hurt.

Counts kernel declarations across **every** active prelude, classifying each by:

- **Provenance** — autonomous producer output · hand-constructed Axeyum proof ·
  imported external proof · replayed/re-admitted existing theorem.
- **Footprint** — empty axiom footprint vs axiom-bearing (read from
  `Kernel::axiom_footprint`, never from source text).
- **Generality** — produced by an operation whose `applicability.fact_ids` names
  **only this fact**. This is mechanically derivable from `operations.json`, so
  it is computed, not self-reported.

Requirements, each of which exists because its absence has already produced a
wrong number in this repository:

1. **Declare coverage.** The tool prints which preludes it built. An empty answer
   from a tool never pointed at your subject is indistinguishable from a strong
   negative result.
2. **Fail on unknown provenance.** A declaration it cannot classify is an error,
   not an "other" bucket.
3. **Deduplicate identities.** Same theorem admitted twice counts once.
4. **Pin by value and ratchet**, in the style of
   `scripts/gen-lean-axiom-ledger.py --check`: a moved number fails with its
   direction, so a rise is a regression to explain and a fall is a result to
   publish.
5. **Negative controls in the test suite** — a fabricated axiom-bearing
   declaration must move the axiom-bearing count; a duplicate must not move the
   total.

*Exit:* `EXPECTED_PRELUDES` covered, committed generated view under
`docs/plan/generated/`, wired into `scripts/flywheel-status.sh`, and the
throughput doc's "nobody can measure this" paragraph replaced by a number.

### P2 — Generality ratchet on the registry — **DONE 2026-08-22**

Both counters live in the provenance ledger above and are gated by value, so a
new single-target capsule cannot move them and a rise is the result:


Two counters, both currently zero, both cheap, both fail-closed:

```text
multi_target_operations   0   -> a rise is the first generality ever measured
facts_via_multi_target    0   -> a rise is the first autonomous yield
```

The ledger's own prose switches when either becomes nonzero, so a report saying
"both are zero" cannot survive a real result — that branch is pinned by a control
that does not touch the classifier, after a first attempt where it was killed by
the classifier's own mutation and therefore pinned nothing new.

### P3 — Producer census — **FIRST RESULT LANDED 2026-08-22**

The census the plan asks for had in fact already been run on 2026-08-19 with a
generic producer, and its funnel is
[`22-mathlib-reflexivity-coverage.md`](22-mathlib-reflexivity-coverage.md):
114 adapter-rejection / 15 producer-decline / 7 kernel-rejection / 2 admissible.
Both middle buckets are now characterised
([`230`](230-producer-decline-shape-census.md),
[`233`](233-adapter-blocker-is-three-theorems.md)), and a second, more capable
producer has landed and been credited:

- [`232`](232-first-general-producer-result.md) — a target-agnostic bounded-induction
  producer proves **three** goals and declines the false control.
- **`multi_target_operations` 0 → 1**, `via_multi_target` 0 → 1.
  `F:ml430-nat-descfactorial-one-d4856d4a` is `proved`, `kernel-lean`, axiom-free,
  the first result here credited to an operation covering more than one fact.
- The must-decline negative controls the plan asked for exist, are gated, and are
  independently recomputed (`must-decline-mutations-v1.json`).

**The dominant cluster is named and is not what the plan assumed.** It is not a
producer capability at all: 113 of the 114 unreachable rows are blocked by three
*theorems* — `congrArg`, `congr`, `mt` — all derivable in our own kernel. That is
P4's target.


Run one genuinely general producer over the dependency-ready train and
development rows under fixed budgets, with held-out untouched. After the P0
repair the evaluation population is train 78 + development 79 = **157**, of
which the census counts 137 open and undispatchable; the dependency-ready
subset is the corpus to freeze. Held-out is **57** rows across three families.

Constraints, all mechanically checkable:

- no theorem-specific code;
- no target-name dispatch tables (P2 enforces this);
- no manually supplied proof plans;
- no proof-body leakage (reuse the existing bubblewrap isolation, already an
  A1-passed requirement);
- one uniform operation across the corpus;
- explicit typed decline reasons for every non-success;
- independent checking and clean replay for every success.

**Pre-register the decline taxonomy before running.** Clusters invented after
the fact will fit whatever happened. Proposed initial classes: unsupported
statement shape · missing reusable theorem · missing algebraic normalization ·
binder/generalization failure · search-budget exhaustion · reconstruction
failure · nonempty axiom footprint.

**Seed the corpus with a negative control set.** A producer evaluated only on
true statements cannot be shown to fail. Include a small number of statements
that **must be declined** — false ones, and true ones whose dependencies are
deliberately withheld. If the producer admits one, the census is void and
reports nothing. This is the 40-of-162 checker-audit lesson applied to
producers, where it has never been applied.

The headline is a funnel, published whatever it says:

```text
88 eligible -> N proposals -> M kernel-accepted -> K cleanly reproduced -> J admitted
```

A poor conversion rate is a result. A conversion rate of zero is a result. The
current honest figure is **1 autonomous theorem**, so almost any measured number
is an improvement in knowledge.

*Exit:* funnel published, declines clustered by pre-registered class, negative
controls all declined.

### P4 — Capability acquisition from the dominant cluster (medium–large)

Take the largest decline cluster from P3 and build the capability that
eliminates **the whole cluster**, not one target. Re-run P3 unchanged; the
delta in the funnel is the value of the capability. Repeat.

This is where doc 17's judgement applies: the statement adapter unlocks all
eight train/development families at once, which is higher leverage than choosing
a familiar theorem and hand-building its route.

### P5 — Held-out evaluation (deferred; scope now reduced)

Only after P4 shows a real improvement on development. Note the permanent cost
of the P0 breach: held-out is **57 clean rows across three families**, not 76
across four, and no later work can restore what was spent.

## Stopping rules

- **Pause SMT parity work** unless a producer failure specifically requires it.
  The cheap levers were measured and are negative — 5× budget converts 1 of 10
  QF_IDL misses; QF_NIA's cheapest levers are 0/+1/+3; portable Alethe is 0-of-85
  ([gap analysis](../plan/gap-analysis-smt-solvers-2026-08-21.md)).
- **Do not reduce the 30 `axreal` axioms.** Nothing on the production path
  reaches them, and 30 is the floor for an axiomatized ordered field, not a dial.
- **Freeze the Fibonacci foundations as reusable substrate and stop extending
  them.** That strand produced **19 of the 24 single-target operations**. The
  reusable value is in the lemmas it left behind — recurrence uniqueness,
  constructive integer induction, constructor laws — not in the operations, none
  of which generalize by construction. Continue only as a controlled comparison
  case for the general producer.
- **Parallel prelude scheduling waits for P1.** It raises activity; without the
  counter it cannot be shown to raise production.

## Decisions requiring an ADR

1. **What counts as autonomous production.** P1's provenance classes become the
   programme's headline metric; the definition must be reviewed, not chosen by
   whoever writes the counter.
2. **How a breached held-out partition is repaired.** P0.2 has two defensible
   answers (reclassify the family, or shrink held-out to 57). The choice is a
   trust-boundary decision and should not be made silently in a JSON edit.

## Reproduction

```sh
# registry coverage vs the ready queue, with a positive control
python3 - <<'PY'
import json, pathlib
ops = json.loads(pathlib.Path("artifacts/autogenesis/operations.json").read_text())["operations"]
cov = {x for o in ops for x in o.get("applicability", {}).get("fact_ids", [])}
F = {json.loads(p.read_text())["id"]: json.loads(p.read_text())
     for p in pathlib.Path("artifacts/facts").glob("*.json")}
settled = {i for i, d in F.items() if d["epistemic_status"] in ("proved", "computed")}
ready = [i for i, d in F.items() if d["epistemic_status"] == "open"
         and all(x in settled for x in d.get("depends_on", []))]
print("multi-fact operations:", sum(1 for o in ops if len(o.get("applicability", {}).get("fact_ids", [])) > 1))
print("ready with an operation:", len(set(ready) & cov))
print("positive control (covered AND settled):", len(cov & settled))
PY

# partition of every fact an operation names
python3 scripts/check-autogenesis-nursery.py --require-ready
python3 scripts/validate-autogenesis-operations.py

# the counters that do exist today
cargo run --release -p axeyum-lean-kernel --example nat_theorem_inventory
cargo run --release -p axeyum-lean-kernel --example int_theorem_inventory
python3 scripts/gen-lean-axiom-ledger.py --check
```

## Relationship to the rest of the programme

- [`02-phased-roadmap.md`](02-phased-roadmap.md) — this plan sequences the next
  increment inside that roadmap; it does not replace its phases.
- [`04-metrics-and-evaluation.md`](04-metrics-and-evaluation.md) — P1 makes
  *autonomous verified yield* computable for the first time. That metric is
  defined there and has never had an instrument.
- [`05-trust-safety-and-governance.md`](05-trust-safety-and-governance.md) —
  P0 is a governance failure, not a bug: an immutability guarantee with no gate.
- [`../../PLAN.md`](../../PLAN.md) remains the sole authority for what is
  actually authorized next.
