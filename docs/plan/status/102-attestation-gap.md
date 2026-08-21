# Lane: attestation-gap — the brief's number was 24x stale, and the real hole was the class nobody checked

<!-- plan-section: lane-status -->

**Not 124 attestations — 5. And a second Lean module that refutes itself, found
in the class the checker's own manifest said was "NOT checked"** (`WIP`,
attestation-gap, 2026-08-18).

Re-measured first. `check-lra-hypothesis-binding.py` reports **135 bound / 102
structural / 73 anchored / 5 attested**, not the `125 BOUND / 124 ATTESTED / 21
DECLINED` the brief carried. That figure came from
`crates/axeyum-solver/src/capabilities.rs`, which had been stale for a day;
lanes 93/94 had already moved 95 of the 124 to `structural` and 9 to `bound`.
The row is corrected. **A stale capability row is how a wrong number becomes a
brief.**

So the gap was closed before this lane started. The prior census generalizes: its
2-rewrite/3-unanchorable split is all that is left, and is understated —
**4 of the 5 are rewrite output**, both `replace_all` rows being a constant-fold.

The live hole was **DECLINED** — 20 instances the manifest listed and nothing
ran on. Two costs, both already paid:

- `extract-concat` rendered `Not (And (Iff prop._24 prop._24) …)` — eleven
  reflexive `Iff`s under one negation, so Lean's `False` follows from that one
  axiom with the `.smt2` file never consulted. The 2026-08-18 self-refutation
  check recognized `Not (Eq α t t)` only, and ran only over attestations.
  Widened to the property and run over every module: **4,652 axioms, 1
  self-refuting.** The emitter now declines it.
- The class is now a two-sided pin, and its first run as a check **evicted two of
  its own members**: the `bug593` rows bind structurally. Reading their φ is the
  lane's other finding — it maps the module's function onto the query's INNER
  `g`, not its outer `f`, so `structural` means *the module names terms this file
  contains*, not *the module says what this file says*.

**The gate is RED at HEAD `570b5c738`, and not from this lane**: 133 of 249
pinned instances fail because `a6ee37c6a` migrated the shipped LRA route to
`CReal` without the checker's carrier vocabulary following. Measured from a clean
snapshot. Migrating it is the reals lane's call; loosening it here is the one
outcome worse than under-covering.

Detail in [`../notes/102-attestation-gap.md`](../notes/102-attestation-gap.md).

<!-- plan-section: landed-changes -->

| 2026-08-18 | `7646b2c04` | `reject_self_refuting_module` at `gate_module_content` — the one boundary every route's module crosses; the Python predicate widened from one shape to the property and run over EVERY class; DECLINED pinned two-sided in its own manifest; the shadowed attested-path copy deleted after the mutation control that used to kill a test reported SURVIVED. 6 mutations, 0 survivors; 9 Rust unit tests, each with its discriminating twin. |
