# Lane: computability — a machine model over ℕ and the halting problem (roadmap W2-14)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, computability, 2026-09-04).** Landed a minimal
step-function register machine (`Nat.RM.runFuel`/`diagStep`/`Halts`,
`nat_prelude/computability.rs`) and `Nat.RM.self_halting_not_decidable`: no
total `H : Nat → Bool` can be correct in both directions about whether
`diagStep H` halts from the marker input `1`. Axiom-free, `Nat` prelude
count 478 (was 474; +4 new declarations), `every_nat_declaration_is_checked_
and_axiom_free` and `check-shape-duplicates.py` both green. ADR-1611 records
the model choice (shallow step-function machine over an explicit
register-machine front end and over `Nat.Partrec.Code`, both rejected/
deferred with cost) and, in detail, the attempt to route the proof literally
through `Nat.cantor_no_fixed_point` and why the shipped proof reuses its
TECHNIQUE (a `Bool.rec`/`Or` case split via `bool_true_or_false`, closed by
`Nat.succ_ne_zero`/`Bool.true_ne_false`) rather than the declared name — the
two cases are Π₁- and Σ₁-shaped respectively and do not share a clean single
fixed point without routing one case through `False.rec` after the
contradiction is already in hand. Fact `F:nat-rm-self-halting-not-decidable`
registered, curated, `validate-facts.py` 0 errors (2409 kernel_facts, 2509
proved). `frontier-shape-census.py` re-run (unrelated shift in its counts).

**What did not land, precisely.** Item 3 of the brief (undecidability of
first-order validity) was correctly sized as out of reach this session — it
needs an arithmetization/reduction project on the scale of the model-theory
reviewer's own roadmap item, not a corollary of the halting result above —
and stays `open` in the ledger with nothing behind it, per instruction. A
full universal-machine formalization (`Nat.Partrec.Code`, reusing the
already-built `Nat.pair`/`unpairLeft`/`unpairRight`) was scoped and named as
the natural next step in ADR-1611 but not built: it is a multi-file project
on the scale of `Nat.Primrec`'s own supporting-theorem stream (ADR-1240).

<!-- plan-section: landed-changes -->

| 2026-09-04 | computability | `nat_prelude/computability.rs`/`computability_tests.rs`: `Nat.RM.runFuel`/`diagStep`/`Halts`/`self_halting_not_decidable`, axiom-free, 5 evaluation tests with negative controls (`d7ddb833e`) |
| 2026-09-04 | computability | ADR-1611: the model choice, the rejected register-machine front end and deferred `Nat.Partrec.Code`, and the Cantor-connection attempt that did not land as a literal function call (`d7ddb833e`) |
| 2026-09-04 | computability | `F:nat-rm-self-halting-not-decidable` fact registered, curated; `frontier-shape-census.py` re-run (`e942c9aee`) |
