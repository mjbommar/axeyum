# Formal Mathematics Tour — Curriculum Knowledge Graph

A structured, machine-readable curriculum for a *formal* tour of mathematics,
derived by working **backward** from three destinations — calculus, number
theory, and linear algebra — to their foundational prerequisites. It exists to
serve axeyum's double-duty thesis
([ADR-0033](../research/09-decisions/adr-0033-double-duty-educational-artifacts.md)):
the same artifacts that teach a concept also test an axeyum theory.

- **🎓 K-12 layer (the school-facing front door):** [`k12/`](k12/README.md) —
  the same backbone projected onto grade bands and a single integrated pedagogy
  (**logic + reasoning + math + computer science as one subject**, with axeyum as
  the self-checking auto-grader). Start with the
  [K-12 vision](k12/README.md), the [four strands](k12/strands.md), and the worked
  modules ([binary & wraparound](k12/modules/binary-and-wraparound.md),
  [truth & counterexamples](k12/modules/truth-and-counterexamples.md)).
- **The graph:** [`curriculum.toml`](curriculum.toml) is the authoritative
  node/edge list (prerequisites = edges) plus per-node decidability/testability
  metadata. The `axeyum-scenarios::mathtour` module mirrors it; tests require
  the graph to stay acyclic, every prerequisite to exist, and every `covered`
  node to name a realized self-checking scenario family.
- **The prose:** one markdown file per node, organized by layer (below). Each
  follows the same template (summary · role · prerequisites/unlocks · *testable
  in axeyum* · Lean-horizon · references).
- **The design rationale:** the
  [formal-mathematics-tour note](../research/08-planning/formal-mathematics-tour.md).
- **The scope ceiling (read this):** [DEPTH.md](DEPTH.md) — what `covered` does
  and does *not* mean (map vs. textbook depth; the decidability ceiling).
- **Canonical texts mapped:** [foundational-books/](foundational-books/README.md)
  — how Spivak and others project onto the LRA / NRA / Lean-horizon split.
- **What to build next:** [BACKLOG.md](BACKLOG.md) — the prioritized 10–20-item
  build list, by yield × readiness.
- **Resource maturity:** the generated
  [curriculum status audit](../foundational-resources/generated/curriculum-status-audit.md)
  distinguishes a curriculum node's exercise status from the maturity of its
  supporting resource packs.
- **Lean-horizon targets:** [reconstruction-targets/](reconstruction-targets/README.md)
  — `∀`-theorems (Peano induction) frozen as proof-track goals, not benchmarks.

## How to read this

The graph is a DAG; a *teaching order* is any topological sort of it. Read
bottom-up (foundations first) to build, or top-down from a destination to see
what it presupposes. Every node names the **decidable/computable fragment**
axeyum can self-check — that fragment is the testable, benchmarkable content;
the rest is flagged Lean-horizon.

### Decidability legend

| Class | Meaning | axeyum handling |
|---|---|---|
| `decidable` | a complete decision procedure exists | self-checked end to end |
| `computable` | the answer is computed, then independently checked | compute-and-verify / witness |
| `bounded` | only finite/fixed instances are decided | exhaustive/sampled, marked |
| `undecidable` | the general case is proof-assistant territory | **Lean-horizon**, never a benchmark |

### Status legend

`covered` — has a self-checking exercise family today · `planned` — testable
fragment identified, family not yet built · `lean-horizon` — primarily a
general-theorem or proof-reconstruction target, not a solver benchmark.

## The layers

### Layer 0 — Foundations (the "bridge")
- [Propositional Logic](00-foundations/propositional-logic.md) · `covered`
- [Predicate Logic](00-foundations/predicate-logic.md) · `covered`
- [Proof Methods](00-foundations/proof-methods.md) · `covered`
- [Mathematical Induction](00-foundations/induction.md) · `covered`
- [Sets](00-foundations/sets.md) · `covered`
- [Relations & Functions](00-foundations/relations-and-functions.md) · `covered`
- [Cardinality](00-foundations/cardinality.md) · `lean-horizon`

### Layer 1 — Number systems
- [Natural Numbers (Peano)](01-number-systems/naturals.md) · `covered`
- [Integers](01-number-systems/integers.md) · `covered`
- [Rational Numbers](01-number-systems/rationals.md) · `covered`
- [Real Numbers](01-number-systems/reals.md) · `covered`
- [Complex Numbers](01-number-systems/complex.md) · `lean-horizon`

### Layer 2 — Core structures & tools
- [Divisibility & the Euclidean Algorithm](02-structures/divisibility-and-euclid.md) · `covered`
- [Modular Arithmetic & Congruences](02-structures/modular-arithmetic.md) · `covered`
- [Groups](02-structures/groups.md) · `covered`
- [Rings](02-structures/rings.md) · `covered`
- [Fields](02-structures/fields.md) · `covered`
- [Polynomials](02-structures/polynomials.md) · `covered`
- [Sequences & Limits](02-structures/sequences-and-limits.md) · `lean-horizon`
- [Counting & Combinatorics](02-structures/counting.md) · `covered`

### Layer 3 — Destinations
- [Number Theory](03-destinations/number-theory.md) · `covered`
- [Linear Algebra](03-destinations/linear-algebra.md) · `covered`
- [Calculus](03-destinations/calculus.md) · `lean-horizon`

## The DAG (prerequisite edges)

```text
propositional-logic ─┬─> predicate-logic ─┐
                     ├─> proof-methods ────┴─> induction ─┐
                     └─> sets ─┬─> relations-and-functions ─┬─> cardinality
                               │                            ├─> groups ─> rings ─┬─> fields ──┐
                               └─> naturals ─> integers ─┬─> rationals ─> reals ─┤            │
                                                         ├─> divisibility-and-euclid ─> modular-arithmetic
                                                         └─> rings                                  │
  reals ─> sequences-and-limits ──────────────┐                                                    │
  rings/fields ─> polynomials ────────────────┼─> calculus                                         │
  divisibility + modular + induction + counting ─> number-theory                                   │
  fields + relations-and-functions + polynomials ─────────────────────────────> linear-algebra ◄───┘
```

(Authoritative edges are in `curriculum.toml`; this ASCII is a reading aid.)

## How status stays honest

`covered` is deliberately narrow: it means at least one mapped exercise family
is realized and self-checking. It does not mean textbook-depth treatment,
complete automation of the general mathematical subject, or a mature resource
pack. The [depth contract](DEPTH.md) defines that boundary, while the generated
[resource audit](../foundational-resources/generated/curriculum-status-audit.md)
reports the separate content-maturity axis.

After changing `curriculum.toml`, its Rust mirror, or linked resource metadata,
run:

```sh
cargo test -p axeyum-scenarios mathtour
just foundational-resources
```

## Why this doubles as testing coverage

The testable fragment of each node maps onto an axeyum arithmetic theory:
number theory → BV/LIA, linear algebra → LRA/NRA, calculus → NRA. Building the
curriculum's self-checking exercises therefore also grows the scenario and
corpus coverage those theories need. The
[example-suites note](../research/08-planning/foundational-example-suites.md)
explains the design rationale; live support and assurance claims belong in the
[support matrix](../research/08-planning/support-matrix.md) and
[capability matrix](../research/08-planning/capability-matrix.md).
