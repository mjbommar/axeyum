# Lane: agent-quantifier-triggers — user-supplied quantifier triggers (`:pattern`, `:weight`)

<!-- plan-section: lane-status -->

**Gap #7 closed for `:pattern`, declined for `:weight` (`DONE`,
agent-quantifier-triggers, 2026-08-21).**
[Gap analysis](../gap-analysis-smt-solvers-2026-08-21.md) §9 row 7. `:pattern`
was parsed and dropped; it is now threaded parse → IR → the E-matching loop and
a usable annotation **replaces** auto-selection ([ADR-0537](../../research/09-decisions/adr-0537-user-triggers-are-a-hint-channel-on-the-arena-and-replace-auto-selection.md)).
Alternatives are unioned, multi-patterns joined, and everything the matcher
cannot fire is declined whole and falls back to auto-selection.

The measurement that motivated it, z3 4.13.3 with its own fallbacks off
(`smt.mbqi=false smt.auto_config=false`): `unsat` unannotated, `unknown` with
`:pattern ((h x))`. Axeyum answered `unsat` for both, in both configurations.

Two findings worth carrying forward rather than re-deriving:

- **The corpus cannot measure this.** 0 of 1430 tracked `.smt2` files contain
  `:pattern` and 0 contain `:weight` (positive control, same command: `assert`
  1419, `forall` 82). The capability delta is zero by construction, and any
  claim about this feature's value has to say so.
- **A verdict is a blunt instrument for "was the trigger obeyed".** Honouring a
  useless trigger did *not* cost the refutation through the front door: term
  invention seeds ground instances of the trigger itself and reaches the witness
  anyway, where z3 with mbqi off has no analogue. The tests measure the proposed
  *instance set* instead.

Next, if this is picked up again: `:weight` needs a corpus that moves under it
before the flood-control cost function is touched (ADR-0537 §5); and the parser
declines any trigger outside an application tree over declared uninterpreted
functions, which rules out arithmetic subterms — the first real workload with
`(f (+ x 1))` as a pattern will want that.

<!-- plan-section: landed-changes -->

| 2026-08-21 | `17079b33d` | `:pattern` was parsed and dropped; the author's trigger now decides. Arena side table, alternatives unioned, multi-patterns joined, declines explicit. ADR-0537. |
