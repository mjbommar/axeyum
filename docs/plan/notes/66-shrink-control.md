# Lane note: shrinking the control, and what it took to verify ADR-0480's route

Detail for [`docs/plan/status/66-shrink-control.md`](../status/66-shrink-control.md).
The decision is [ADR-0486](../../research/09-decisions/adr-0486-a-negative-control-is-one-assumed-law-over-a-constructed-carrier.md).

## The measurement that discharges the specification

`generalize_over_ordered_ring` builds each ring binder's type as
`abstract_consts(declared_type, telescope[..i])` — a function of the signature's
30 declaration *types* alone. `ring_interface_telescope` lifts that out of the
generalization so it can be computed from any `RingSignature` without a
refutation, and `the_standalone_telescope_is_the_generalized_statements_own_prefix`
pins the two together by `ExprId` identity in one kernel, so the standalone form
is the shipped statement's own prefix rather than a lookalike built beside it.

`examples/ring_interface_pin.rs` then reads the telescope off `Real` (30 axioms)
and off `Int` (30 proved declarations, trusted surface 0) and compares the
rendered types byte for byte:

```text
ring interface telescope: 30 binders, 30 identical, 0 differing
```

The rows are emitted as `source<TAB>binder<TAB>declaration<TAB>hex`, the same
shape `prelude_axiom_inventory` emits, so the ledger can digest them by the same
rule when the pin is moved.

**Why this is the right measurement and not a tautology.** Abstraction replaces
`Real`/`Int` and their operations by the *same* bound variables, so if the two
developments state the same laws the abstracted types coincide — and if they do
not, they differ. The example prints the `source` column for exactly that
reason: the test asserts `real[0].source` starts with `Real` and
`integer[0].source` with `Int`, so "identical" is never the identity of a
telescope compared with itself.

## Two things I got wrong first, both worth keeping

**A `NameId` is an INDEX.** My first presence-guard test carried the `Real`
signature into a kernel holding the `Int` development, expecting a refusal. It
got 30 well-formed binders sourced from `Nat.le`, `Nat.beq_refl`, `Nat.pow_succ`
and `Nat.divModState`, and no error. Cross-kernel handle reuse does not fail; it
silently resolves to whatever sits at those indices. `validate_in` is the guard
that sees it, presence is not, and the docs now say the narrow thing rather than
implying the broad one. The error path also had to stop calling `display_name`
on a name the kernel never interned — that panics rather than returning the
refusal.

**A guard that no test can kill.** The first `build_control_carrier` checked
that the control axiom's discharge is footprint-empty, and deleting that check
killed **zero** tests: nothing reachable from the public API could produce a
non-axiom-free discharge. `control_carrier_over` was split out so a test can
hand it the `Real` package's interface — where the discharge rests on
`Real.lt_irrefl` — and the guard now kills exactly one test. That split is
load-bearing.

## Mutation results

| mutation | tests killed |
|---|---|
| control axiom points at `le_trans` (a law no fixture reaches) | 1 — `a_refutation_reaches_the_control_axiom_and_nothing_over_the_integers` |
| discharge-is-axiom-free guard deleted | 1 — `a_control_built_on_an_assumed_law_is_refused` |
| signature slot not swapped (control declared, never used) | 1 — `a_refutation_reaches_the_control_axiom_and_nothing_over_the_integers` |
| `le_refl`/`le_trans` transposed in `From<IntPrelude>` | `ring_interface_pin --require-identical` → `28 identical, 2 differing`, exit 1 |

Every run also failed `end_to_end_reflexive_disequality_reconstructs_directly`,
which is another lane's uncommitted `reject_self_refuting_module` in the shared
worktree and fails unmutated too. Baseline `-p axeyum-solver --lib --features
full`: 1208 → 1212 (three telescope tests, four control tests; the count drifted
upward mid-lane as other lanes landed).

## What is left, in the order it has to happen

1. Re-express `build_int_model_of_arith`, `build_rat_model_of_arith` and
   `build_creal_model_of_arith` as instantiations of the telescope rather than
   interpretations of 30 axioms. `F:real-axioms-modelled-by-constructed-setoid`
   and its ℤ/ℚ siblings ride on these and must be restated, not dropped.
2. Give `arith_prelude_builds()` and `F:shipped-front-door-reaches-no-real-axiom`
   a home that survives the package's removal — *reached* is ADR-0480's second
   published number and cannot simply lapse.
3. Move the ledger's digest pin onto the telescope, and put
   `ring_interface_pin --require-identical` in the aggregate gate **before** the
   move, not after.
4. Promote the control to a prelude the ledger measures and swap the population
   `real: 30` → `control: 1` in **one** `--accept-population-change` run. Doing
   it in two publishes a trusted surface of 31 in between.

## Gates this lane did NOT run, and why

Six lanes were queued on `scripts/cargo-serialized.sh`'s flock when this lane
finished, and the following never reached the front of it. They are recorded as
**not run**, not as passing:

`-p axeyum-lean-kernel --lib` · `front_door_carrier --require-axiom-free` ·
`ordered_ring_refutation --require-empty` and `--constructed-reals` ·
`--test farkas_over_the_integers` · `--test front_door_reaches_no_real_axiom` ·
`RUSTDOCFLAGS="-D warnings" cargo doc` · `gen-lean-axiom-ledger.py --check` ·
`check-prelude-reuse-equivalence.sh`.

What *did* run on a snapshot of the exact committed tree: `+stable clippy
--workspace --all-targets --all-features -- -D warnings` **exit 0** — the gate
that has red-ed `main` twice in a day, and the one most likely to be broken by a
new module — plus `-p axeyum-solver --lib --features full`, `check-links.sh`,
`validate-facts.py`, `check-fact-derived-numbers.py`, `gen-adr-index.py --check`
and `gen-plan.py --check`.

The argument for the untried ones is that this lane adds a module and an example
to `axeyum-solver` and changes no kernel code. That is an argument, not a
measurement, which is why it is written here rather than in the status block.

Two failures seen throughout, neither from this lane and both present unmutated:

- `end_to_end_reflexive_disequality_reconstructs_directly` fails against another
  lane's uncommitted `reject_self_refuting_module` in the shared worktree;
- `crates/axeyum-lean-kernel/src/lean_pp.rs` reds STABLE clippy in the worktree
  (`too_many_arguments`, 8/7) from an edit that is in no commit — which is why
  the clippy run above had to be done on a `lane-snapshot.sh` extraction of the
  commit rather than on the working tree.

## Neither of the two examples this ADR reasons about is in any gate

`front_door_carrier --require-axiom-free` and `ordered_ring_refutation
--require-empty` are treated as gates by ADR-0480 and by the lane briefs built
on it. Measured 2026-08-18: `grep` for `require-axiom-free`, `require-empty` and
`constructed-reals` across `scripts/*.sh`, the `justfile` and
`.github/workflows/` finds **zero** invocations. They are commands lanes are
told to run, and nothing runs them otherwise. `ring_interface_pin
--require-identical` is in the same position, deliberately — wiring one of the
three and not the others would be worse — but the whole set belongs in the
aggregate gate before the ledger's pin moves onto the telescope.
