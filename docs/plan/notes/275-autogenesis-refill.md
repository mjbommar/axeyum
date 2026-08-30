# Notes: 275-autogenesis-refill

Detail moved out of [`../status/275-autogenesis-refill.md`](../status/275-autogenesis-refill.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

> Of the open facts, 15 can NEVER be closed: 12 MUTATION negative control(s) …
> and 3 pinned open by a gate that fails if the status moves.

But its four headline counts are **research 3 / blocked 17 / backlog 47 /
novel 2**, and every one of them includes held-out and mutation rows. There is
no count anywhere in its output of *rows a lane may actually be dispatched at*.
It exits 0 whatever it finds.

It does carry one emptiness alarm — `if not research: print("The frontier is
EMPTY…")` — scoped to the **research frontier** band only. That band is 3
(Collatz, Goldbach, twin primes) and will not empty, so the alarm cannot fire
for the failure that actually occurred. It is also a `print`, not an exit
status.

### `scripts/create-autogenesis-nursery-dispatch-baseline.py` — the near miss

This one *does* carry a counter that can reach zero: `coverage.eligible_for_
dispatch`, pinned in `artifacts/autogenesis/mathlib-nursery-dispatch-baseline-v1.json`.
Three problems, in increasing order of importance:

- The pinned value is **2**, alongside `already_established: 31` — against a
  current 155 proved. The pin is far out of date.
- `--check` is therefore **RED**, printing `dispatch baseline is stale;
  regenerate without --check` and exiting 1. It is registered in *both*
  `scripts/check.sh` (step `autogenesis-nursery-dispatch-baseline`) and the
  `justfile`. This is red on `main`: the script reads only `nursery-v1.json`,
  `operations.json`, `artifacts/facts/` and the statement adapters, and this
  lane's diff touches none of them. Third instance of the pattern this
  repository already records (`check-kernel-stack-envelope.sh --check` was
  another): *a gate is red and nobody has run it.*
- Even regenerated, it would not answer the question. Its
  `eligible_for_dispatch` counts facts with an **exact authoritative operation**
  registered — producer coverage. A row with no operation is `declined-before-
  execution` (all 144 of them, reason `no-exact-authoritative-operation`),
  which is not the same as *structurally unclosable*. Both numbers can be zero
  for unrelated reasons and only one of them means the queue is empty.

### `scripts/gen-production-provenance-ledger.py`, `check-curriculum-coverage.py`

Neither computes a dispatchable count. The provenance ledger's guarded counters
are about operation *generality* (`applicability.fact_ids` length), which is the
upstream defect this repository already records; curriculum coverage is a topic
DAG and does not consult partitions.

### What landed

`scripts/check-dispatchable-frontier.py`. It computes

```
open ml430 rows
  - held-out          (blind evaluation, ADR-0542 — off-limits, not unclosable)
  - mutation controls (deliberately perturbed; never closable by design)
  - structurally blocked (mirror-divergence registry, below)
  = DISPATCHABLE
```

and **exits 1 when that set is empty** (guard G4). There is no floor to lower
and no threshold to tune: the only way through the gate is to add population
that can actually be worked. Below `NARROW = 3` it prints a warning rather than
failing, because failing on a healthy-but-narrow queue is how a gate gets
ignored.

Today's output:

```
open ml430 mirrors: 59
  held-out (blind evaluation, do not dispatch): 35
  mutation negative controls (never closable):  12
  structurally blocked by a divergence:         11
  DISPATCHABLE:                                 1
      F:ml430-nat-lt-xor-cases-c43a1e85
WARNING: only 1 dispatchable mirror(s) remain.
```

(35, not 37: two open held-out rows are *also* mutation controls, and the
classification reports the mutation, which is the stronger reason. 35 + 12 + 11
+ 1 = 59.)

---

## (2) The divergence screen, applied before preregistration

`artifacts/autogenesis/mirror-divergence-registry.json` — one row per Mathlib
construction whose axeyum counterpart diverges, carrying the class, the reason,
and where the reading is recorded.

`check-dispatchable-frontier.py --screen <candidates.json>` runs it over
candidate propositions and exits 1 if any is blocked, so the check happens
*before* a generator preregisters unclosable population.

### The obvious mechanisation is wrong, and the gate's own guard proves it

The codomain class looks derivable from the pinned statement alone: flag any
Bool-position token. **It is a false-positive machine here.** `&&&` (Nat AND)
contains `&&`; `|||` contains `||`. Measured over the ledger, eight
**already-proved** `ml430` bitwise facts carry those substrings —
`land_assoc`, `land_comm`, `land_bit`, `lor_assoc`, `lor_comm`, `lor_bit`,
`ldiff_bit`, `bitwise_bit` — and `Nat.land_bit`'s `(a && b)` is a *genuine*
Bool that we proved. Bool is not the divergence; `Nat.testBit`'s codomain is.

So the registry names the **construction**, and the gate carries guards that
stop the registry from being used to shrink the open count by assertion:

| guard | what it prevents |
| --- | --- |
| **G1** stale entry | a blocker that matches no `ml430` proposition at all |
| **G2** unwitnessed codomain | a `codomain` claim with no pinned statement placing the construction against a `true`/`false` literal — the claim must be **re-derived from the pinned source**, not asserted. `Nat.testBit` is witnessed twice (`lt_of_testBit`, `zero_of_testBit_eq_false`). |
| **G3** blocks a settled mirror | the false-positive control: the registry may never block a mirror we already proved. Runs against all 155 closed rows on every invocation, not against a fixture. |
| **G5** unbacked non-codomain claim | definitional / algorithmic / recursion-principle divergences live in the *definition* and are invisible in the pinned statement, so this gate **cannot** re-derive them. It instead demands a `mathlib_source.path` and a `recorded_in` document that exists in the tree. Stated as a limitation, not papered over. |
| **G6** blocked candidate | `--screen` rejects a candidate before preregistration |

Controls: `scripts/tests/test-dispatchable-frontier.sh`, 12 cases, registered in
`scripts/check.sh` **and** the `justfile` (`check-control-registration.sh`: 25
controls, 0 orphans). Every case asserts both that its own guard fired and that
no other did. Mutation-verified in a `copytree`'d scratch tree: nine mutants,
each killed by exactly one case. Two false-positive controls — a healthy
synthetic fixture, and the real repository tree.

**Mutation testing earned its keep here.** The first draft's controls could not
reach two guard branches — a `codomain` entry with *no witness regex at all*,
and a non-codomain entry naming *no Mathlib source* — both deletable with every
case still green. Two cases added; both mutants now die. That is precisely the
"the technique measures the guards you have" caveat, caught on the guards this
lane wrote.

### The screen at scale

Run over the **entire unused pinned supply** — 8,819 propositions, see (3) —
the registry blocks **142**:

```
Nat.testBit      codomain              72
Nat.minFac       algorithmic           43
Nat.fastFib      recursion-principle   19
Nat.multichoose  definitional           8
```

Those are the rows a naive generator would have preregistered as unclosable
population — roughly **twelve times the current dispatchable inventory**, added
as open count with no work in it. And 142 is a **lower bound**: the registry
knows four constructions, and the four are the ones the ledger has already run
into.

---

## (3) Refilling the population — proposal, not executed

### The supply is not the bottleneck

`artifacts/autogenesis/mathlib-statement-source-v1.json` pins a statement-only
inventory at Mathlib `c5ea0035…` / v4.30.0 (9,729 `Nat.`/`Int.` theorem
records, on disk at
`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-nat-int-statement-inventory-v1.ndjson`).
Measured:

```
pinned theorem records                       9,729
after dropping compiler-generated names      9,021
already in the ml430 catalog                   202   (the other 12 are mutations)
unused supply                                8,819
```

The nursery policy's `evaluation_fact_count.maximum` is **300** against 216
entries today, so there is headroom for ~84 more before the ceiling — the
policy, not the supply, is the near-term binding constraint.

### What `screened-ok` does and does not mean

**8,677 of 8,819 pass the divergence screen, and that is a necessary condition,
not a sufficient one.** The screen answers "does this mirror a construction we
know diverges". It does not answer "is this statable in our kernel at all". The
module distribution of the unused supply makes that gap obvious:

```
557  Init.Data.Int.DivMod.Lemmas
510  Init.Data.Range.Polymorphic.NatLemmas
472  Init.Data.Nat.Lemmas
419  Init.Data.Int.Order
333  Init.Data.Range.Polymorphic.IntLemmas
327  Init.Data.Nat.Basic
206  Init.Data.Int.Gcd
174  Mathlib.Algebra.Order.Floor.Ring
```

`Range.Polymorphic`, `Floor.Ring` and `Nat.Partrec` are over structures this
kernel does not have. **A refill needs a second, positive screen — "statable
here" — which this lane did not build**, and which is the natural next task: it
must read the environment (`kernel.environment()`), not a theorem inventory,
since `prelude_theorem_inventory` lists no `Definition`s.

### Constraints a refill must respect

1. **Do not modify any existing entry's partition.** The repair discipline for
   a spent row is an amendment ledger (ADR-0542), never a deletion or a
   reassignment made for convenience. Two amendments exist
   (`natural-gcd` 2026-08-22, `natural-binomial` 2026-08-25) and both are marked
   `irreversible: true`.
2. **`partition_unit` is `whole-family-with-source-review-groups-indivisible`.**
   Adding a proposition to an *existing* family inherits that family's partition
   automatically and does not disturb the split. Adding a proposition to
   `natural-logarithm` or `natural-square-root` grows the held-out population
   without spending any of it. Adding to `natural-bitwise` or `natural-primes`
   adds dispatchable work. Both are safe; they do different jobs.
3. **A NEW family needs its partition assigned before target outcomes are
   known** (`split_freeze: before-target-outcomes`). That is the hard part and
   it is a discipline question, not a tooling one: the assignment must be made
   without consulting whether we can prove the members. Drawing new families
   from Mathlib areas nobody here has worked is what makes that credible.
4. `check-autogenesis-holdout-isolation.py` must stay green. Run before and
   after — **PASS both times in this lane** (`held_out=37, files_scanned=1103,
   settled=0, references=0`); this lane added no fact and touched no partition,
   so the number is unchanged by construction and the check is a control on that
   claim rather than evidence of care.

### Proposed sequence

1. Build the "statable here" positive screen (reads the kernel environment).
2. Run **both** screens over the 8,819 and rank what survives by family.
3. Propose a refill of ~80 propositions (staying under the 300 ceiling) as
   *whole families*, split between existing dispatchable families and at least
   two genuinely new ones.
4. Assign the new families' partitions **and record the assignment** before any
   of them is looked at, with the same `state:
   preregistered-before-target-outcomes-with-recorded-amendments` discipline.
5. Regenerate via `create-autogenesis-mathlib-nursery-split.py --check` and
   re-run the isolation and dispatch-baseline gates. **Fix the stale dispatch
   baseline first** — regenerating it as part of a refill would hide a
   pre-existing red inside a large diff.

### What this lane did NOT do

**No population was preregistered.** Step (1) above is a real prerequisite, the
nursery is in `state: frozen-evaluation` with a `source_catalog_sha256` pin, and
the brief's instruction was explicit: do not preregister unilaterally if the
isolation constraints are at risk. Choosing partitions for new families is a
decision that should be recorded as an ADR amendment, by someone who has not
just spent an afternoon looking at which of the candidates look easy.

---

## (4) The measurement drift, and how the ledger should count a local analogue

### Measured

Eight **proved local facts** name a registry-blocked open mirror in their
`notes`, covering 7 of the 11 blocked rows:

```
F:nat-binary-rec-fuel-irrelevance  -> F:ml430-nat-fastfib-eq
F:nat-binary-rec-succ              -> F:ml430-nat-fastfib-eq
F:nat-coprime-of-lt-minfac         -> F:ml430-nat-coprime-of-lt-minfac
F:nat-lt-of-testbit                -> F:ml430-nat-lt-of-testbit
F:nat-multichoose-one              -> F:ml430-nat-multichoose-one
F:nat-multichoose-one-right        -> F:ml430-nat-multichoose-one-right
F:nat-multichoose-zero-right       -> F:ml430-nat-multichoose-{one,one-right,zero-right}
F:nat-zero-of-testbit-eq-zero      -> F:ml430-nat-zero-of-testbit-eq-false
```

Uncovered: `testbit_land`, `testbit_lor`, `testbit_ldiff`, `testbit_eq_inth` —
the four needing the `Nat.bit` decode bridge.

Widening to *any* non-mirror fact whose notes mention any `F:ml430-*` id gives
**55**, all proved, of which only 8 use the word "analogue". So the relationship
is recorded in free prose, inconsistently, and the ledger's own metric cannot
see it. The mirror count says 155/214 and the work these 55 represent is
invisible to it.

### Why prose-mining is not the fix

The scan above needed a regex over `notes`, and a naive `F:ml430-[a-z0-9-]+`
pattern **matches strings that are not fact ids**. Measured: **18** non-mirror
facts yield at least one such string, **10** distinct:

```
F:ml430-nat                    F:ml430-nat-land          F:ml430-nat-lor
F:ml430-nat-bitwise            F:ml430-nat-descfactorial  F:ml430-nat-sqrt
F:ml430-nat-ascfactorial-one   F:ml430-nat-land-bit
F:ml430-nat-ldiff-bit          F:ml430-nat-lor-bit
```

The first six are prose wildcards, and those are the harmless half. The other
four — `ascfactorial-one`, `land-bit`, `ldiff-bit`, `lor-bit` — read as
*complete* ids that merely omit the hash suffix, so nothing about them looks
truncated. The measurement had to filter every hit against the real fact ids to
be trustworthy. A metric derived from prose would be wrong in a way nobody would
notice, which is the failure this repository cares most about.

### Proposal: a structural link, and two numbers that never merge

The fact schema is `additionalProperties: false`, so this needs a schema
addition. Proposed optional block:

```json
"mirror_relation": {
  "mirror": "F:ml430-nat-lt-of-testbit-72f64ab8",
  "relation": "local-analogue",
  "diverging_construction": "Nat.testBit",
  "divergence_class": "codomain"
}
```

`relation` ∈ `{"local-analogue", "partial-support"}`. There is deliberately **no
`"flip"` value**: a mirror we can honestly close gets its own status flipped, and
a relation field is not where that is recorded.

Gate rules, extending `check-dispatchable-frontier.py`:

- **A1** the named `mirror` must exist and be an `F:ml430-*` fact.
- **A2** for `relation: "local-analogue"`, the mirror must be classified
  **blocked** by the registry, with `divergence_class` equal to the registry's
  class for `diverging_construction`. *This is the guard that matters*: without
  it a lane could land a local fact, declare it an analogue of a perfectly
  dispatchable mirror, and score credit for dodging closable work. The
  registry's own G1–G3 then make A2 non-circular — the block has to be
  witnessed.
- **A3** an analogue may never change the mirror's `epistemic_status`, and the
  reported numbers stay separate:

  ```
  mirror closures      155 / 214      (unchanged, comparable, what a referee checks)
  structural analogues   8 local facts covering 7 of 11 blocked mirrors
  ```

  Never summed. A derived "addressed" figure may be printed **only** with both
  components beside it, so it cannot be quoted as a closure rate.
- **A4** a `local-analogue` whose mirror later becomes *dispatchable* (the
  registry entry is removed, or the construction is reconciled) fails the gate
  — the analogue then needs re-examination, since the mirror may now be
  closable.

The nursery should record the same thing append-only: an entry gains
`outcome: "structural-analogue"` with the local fact id, **never** a partition
change. That keeps ADR-0542's discipline intact and makes the blind-evaluation
bookkeeping honest about rows that were worked but not closed.

This lane did not implement (4): it is a schema change to
`artifacts/ontology/fact.schema.json` plus a `validate-facts.py` rule plus
retro-fitting 8 (or 55) facts, and it should land as one deliberate change
rather than as a tail on a gate commit.

---

## Checks run (foreground)

| check | result |
| --- | --- |
| `scripts/tests/test-dispatchable-frontier.sh` | 12/12 pass |
| mutation verification (copied tree, 9 mutants) | each killed by exactly one case |
| `scripts/check-dispatchable-frontier.py` | exit 0, dispatchable 1 (+ WARNING) |
| `scripts/check-control-registration.sh` | exit 0, 25 controls, 0 orphans |
| `python3 scripts/validate-facts.py` | exit 0, **0 errors** |
| `python3 scripts/check-autogenesis-holdout-isolation.py` | PASS, `held_out=37 … references=0` (before and after) |
| `cargo fmt --all --check` | not run — this lane touched no Rust |
| `create-autogenesis-nursery-dispatch-baseline.py --check` | **exit 1, stale — pre-existing on `main`, not caused here** |
