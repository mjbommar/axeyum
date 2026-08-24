# 250 — Natural modular-equivalence capability selection

The first bounded target selected from the new knowledge artifacts is not an
individual theorem. It is the three-fact, dependency-ready core of natural
modular equivalence: `Nat.ModEq.refl`, `Nat.ModEq.symm`, and
`Nat.ModEq.trans`. The fourth law, commutativity, remains explicitly deferred
because the ledger says it depends on symmetry.

This is a legitimate capability candidate because the existing target-agnostic
Eq/Iff combinator producer was already measured against all four Natural-number
development statement streams: their adapters imported cleanly and axiom-free.
The remaining gap is authoritative source-bound receipt and registration, not a
license to assert that the existing Int operation applies to Nat.

The selection artifact binds the three exact open facts, the deferred dependency,
the current absence of an operation covering them, and construction constraints
that forbid target-name dispatch or unaudited applicability expansion. If any of
those facts becomes settled or operation-covered, its checker fails rather than
silently selecting stale work.

```sh
python3 -m unittest scripts.tests.test_validate_autogenesis_nat_modeq_capability_selection
python3 scripts/validate-autogenesis-nat-modeq-capability-selection.py
```
