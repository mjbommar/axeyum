# ADR-0453: Route-Dependent Provability — Which Logic Does Axeyum Prove In?

Status: proposed
Index-summary: Two proof routes prove different theorems; keep the kernel constructive and make classicality an explicit, recorded assumption
Date: 2026-08-14

Requirements: [north-star note](../00-orientation/north-star.md) — "a complete
framework for general reasoning, logic, and proving".

## Context

Axeyum settles a proposition by one of several routes, and this ADR exists
because **they do not prove the same theorems**. That was discovered by
measurement on 2026-08-14, not by design, and nothing in the stack records it.

`build_logic_prelude` declares exactly `True`, `False`, `And`, `Or`, `Iff`,
`Not` (as `a -> False`), `Eq` and `Exists`. Enumerating the environment it
produces gives **zero trusted declarations of any kind** — no `Axiom`, no
`Opaque`, no `Quotient`:

```
logic:   axiom=0  opaque=0  quotient=0  total_trusted=0
nat:     axiom=0  opaque=0  quotient=0  total_trusted=0
```

There is no `propext`, no `Classical.choice`, no `Quot.sound` — the three Lean
itself reports — and no `Classical.em`. The kernel route is therefore
**intuitionistic**. That is a strength: it is what makes `axiom_footprint: []`
on 17 facts a real and unusually strong claim.

The SMT term-level route decides a propositional query by exhaustive evaluation
in the `axeyum-ir` evaluator, over **classical two-valued boolean semantics**.

The consequence is concrete and was hit immediately by an extraction lane
working the `S:logic-and-proof` strand:

| proposition | `smt-term-level` | `kernel-lean` |
|---|---|---|
| De Morgan's laws | proved | provable constructively |
| excluded middle `p ∨ ¬p` | **proved** | **not reachable without a new axiom** |
| double-negation elimination | **proved** | **not reachable without a new axiom** |
| Peirce's law | **proved** | **not reachable without a new axiom** |

A reconstruction pipeline that pipes an SMT `unsat` into the kernel therefore
hits a wall on *every classical tautology*, and today it does so opaquely — the
kernel simply fails, with nothing saying why or that the failure was structural
rather than a missing lemma.

A second symptom appeared in the fact ledger. `axiom_footprint` was carrying two
incompatible vocabularies with nothing marking the difference: 17 facts with
`[]` from the kernel and 14 with `["axeyum-ir.bool-evaluator",
"classical-two-valued-bool-semantics"]` — strings a lane had to invent because
the schema offered none. Read side by side the first group looks like it rests
on less. It does not; they are different trust bases, and the routes are not
even of equal strength.

## Decision

**Proposed, and explicitly the maintainer's call — this ADR records a measured
situation and a recommendation, it does not close the question.**

1. **Keep the kernel route constructive.** Do not add classical principles to
   `build_logic_prelude` by default. Axiom-freedom is the project's headline
   metric and it is only meaningful because the constructive core is genuinely
   assumption-free.

2. **Make classicality an explicit, recorded assumption where it is needed.**
   When a development requires excluded middle, admit the axiom deliberately and
   let it appear in `Kernel::axiom_footprint`. This is Lean's own arrangement:
   `Classical.em` is derived from `Classical.choice` and `propext`, and
   `#print axioms` reports it. A proof that needs classical logic should *say
   so* in a machine-readable way, not be silently unavailable.

3. **Record the route on every settled fact.** Implemented already: `proof_route`
   is required on any `proved`/`computed`/`refuted` fact, and
   `axiom_footprint: []` is rejected on any route that cannot deliver
   axiom-freedom. Axiom-freedom is reported scoped to `kernel-lean` rather than
   as a cross-route total, since that total is exactly the conflation above.

4. **Make the reconstruction wall diagnostic rather than opaque.** When kernel
   reconstruction of an SMT result fails, it should be able to report "this
   proposition is classically but not intuitionistically valid" as a specific
   outcome. Not yet implemented; this is the actionable follow-up.

## Evidence

- `cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory` — the
  logic/nat trusted-surface counts quoted above, over `Axiom`, `Opaque` and
  `Quotient` rather than `Axiom` alone.
- `python3 scripts/validate-facts.py` — route spread
  `kernel-lean=17 search-certificate=2 smt-term-level=14`, and the 14
  SMT-route footprints naming the evaluator's semantic assumptions.
- `F:excluded-middle`, `F:double-negation-elimination`, `F:peirce-law` — proved
  on the SMT route, each cross-checked against z3 and re-derived against a fresh
  parse. `F:excluded-middle-not-intuitionistic` was landed by that lane
  specifically to hold this gap open, with `formal.fragment: "none"` because
  nothing here can currently state it.
- `docs/facts-extraction-2026-08-14/diary-facts-logic.md`, "Gap B — one logic per
  route, and nothing that records the difference".

## Consequences

**Accepted cost.** Some propositions will be `proved` on one route and `open` on
another, and the ledger will show that rather than hide it. This looks like
inconsistency and is not: it is the honest state of a system with more than one
trusted checker.

**What this buys.** `axiom_footprint: []` keeps its strong meaning. A consumer
can ask "what does this rest on" and get a route-scoped answer instead of a
number that silently mixes two scales.

**What is still open.** Whether a *deep embedding* of formulas and derivations
(a `Formula` inductive in the kernel, using the existing
`add_recursive_datatype_family`) should be built so that metatheorems — "there
is no intuitionistic derivation of `p ∨ ¬p`" — become statable rather than
merely assertable in prose. That would turn the table above from a note in an
ADR into checked facts. It is the single largest missing capability the logic
strand identified, and it is deliberately NOT decided here.
