# ADR-1500: A soundness fix is not pinned until a control dies without it — and its admission controls must be observable in the same run

Status: accepted
Date: 2026-09-01
Index-summary: ADR-1495 closed a `Type : Type` hole in
`Kernel::add_inductive` — Lean's `check_constructor` universe constraint,
`KernelError::ConstructorFieldUniverseTooBig` — and the fix shipped with its
rejection assertion and both admission controls inside ONE `#[test]`.
Independently reproduced here: disabling the guard leaves
`kernel_seam_fuzz`, `mutual_inductive_group_grammar` and
`nested_inductive_grammar` all at **1 passed, exit 0**, because ADR-1495's own
fixture change moved the generators to emitting only Lean-legal shapes. What
DOES die is `--lib inductive`, whose single bundled test the coordinator's
measurement did not run — so the guard was pinned, by exactly one test, and
nobody had shown it. That test measured less than it appeared to: it fails on
its FIRST assertion, so its two admission controls were unreachable in the only
configuration where their answer matters. Split into seven `#[test]`s plus an
ordering control, each reported with AND without the guard, and registered in
`scripts/tests/mutation_controls.py` as `inductive-universe-guard` with two
mutations that fail in opposite directions (guard removed: 2 tests die; `Prop`
exemption removed: 6 die). Two findings beyond the pin. **Nothing checked that
`Prop`'s exemption is sound rather than merely present** — it is sound because
`allows_large_elimination` separately denies large elimination to a `Prop`
family exposing a non-proof field, and no test connected the two; that is now
`prop_exemption_is_sound_because_large_elimination_is_denied`, with a fieldless
`True`-like singleton as its non-vacuity control. And the check ORDER is the
reverse of what `reject_ctor_wrong_param`'s doc comment implies: positivity is
a whole separate PRE-PASS over every constructor, so it masks the universe
error even when the universe-illegal field comes first. Decision on restoring
illegal coverage to the grammar generators: **follow-on, not this lane** — the
axis is cheap but the byte-pinned 360-case digest and that masking interaction
are not, and regenerating the digest in the same commit that changes it is the
"editing a file that pins its own digest" failure.
Index-status: accepted

## Context

ADR-1495 found and fixed a real soundness hole in this project's single trust
anchor. Without the constraint, `add_inductive` accepted

```
U : Sort 1        with        mk : Sort 1 → U
```

Large elimination then yields `el : U → Sort 1` with `el (mk X)` def-eq `X`,
making `Sort u` a retract of an inhabitant of `Sort u` — the `Type : Type`
precondition for Girard's paradox, from which `False` is derivable. Everything
downstream of `Kernel::add_declaration` — every axiom-free result, the graded
statement families of ADR-0603, the dominance argument — rests on that gate
refusing what it should refuse.

The fix is eight lines in `inductive.rs`:

```rust
if !self.level_is_zero(group.result_level)
    && !self.level_leq(domain_level, group.result_level)
{
    return Err(KernelError::ConstructorFieldUniverseTooBig { … });
}
```

`Prop` is exempt because it is impredicative.

The question this ADR answers is not whether the fix is right. It is whether
anything would notice its removal.

## What was measured

### The surviving mutant, reproduced independently

In an isolated snapshot (`scripts/lane-snapshot.sh`, never the shared tree),
the guard's first conjunct was replaced by `false`, making the whole `if` dead:

| suite | with guard | guard disabled |
| --- | --- | --- |
| `--test kernel_seam_fuzz` | 1 passed | **1 passed, exit 0 — SURVIVED** |
| `--test mutual_inductive_group_grammar` | 1 passed | **1 passed, exit 0 — SURVIVED** |
| `--test nested_inductive_grammar` | 1 passed | **1 passed, exit 0 — SURVIVED** |

Confirmed. The reason is in ADR-1495's own fixture change: the grammar
generators' `Type` families were moved from `Sort 1` to `Sort 2` so that their
`Sort 1` constructor fields are legal. That correctly stopped the fixture
*asserting the bug* — before ADR-1495 it emitted 720 cases of which the
`type`-sorted ones were Lean-illegal and asserted to ADMIT — but the suites now
generate only legal inductives, so they cannot exercise the guard at all.

### What the coordinator's measurement did not run

`cargo test -p axeyum-lean-kernel --lib inductive` **does** die. ADR-1495 landed
`reject_ctor_field_universe_above_result_universe`, which builds the illegal
inductive directly and asserts the error. So the guard was not unpinned; it was
pinned by exactly one test that the three-suite sweep did not include.

This is the standing "`--lib` is not a sufficient pre-merge gate" trap running
in the other direction, and it is worth naming as such: **integration suites are
not a sufficient mutation target either.** A mutation sweep is only as wide as
the suites it runs, and choosing them from "which files did the fix touch"
selects the suites whose fixtures the fix *repaired* rather than the ones that
test it.

### What that one test could not tell anyone

It carried three assertions in one `#[test]`:

1. `U : Sort 1` with `mk : Sort 1 → U` ⇒ refused;
2. `W : Sort 2` with `mk : Sort 1 → W` ⇒ admitted;
3. `P : Prop` with `mk : Sort 1 → P` ⇒ admitted.

Assertions 2 and 3 are the direction-of-refusal controls — a guard that refuses
too much is also a defect, and this one sits in the path of all 98
`add_inductive` call sites. But the test dies on assertion 1 the moment the
guard is removed, so **2 and 3 are never reached in the configuration whose
answer they exist to give.** A control bundled behind a failing assertion
measures nothing about the failing configuration.

### The split, with both configurations stated

Seven `#[test]`s plus one ordering control, each run with the guard and with
the guard disabled:

| control | with guard | guard disabled |
| --- | --- | --- |
| `reject_ctor_field_universe_above_result_universe` | pass | **FAIL (pin)** |
| `reject_ctor_field_universe_above_result_universe_polymorphic` | pass | **FAIL (pin)** |
| `admit_sort1_field_under_sort2_family` | pass | pass |
| `admit_bundled_sort2_structure_with_sort1_carrier` | pass | pass |
| `admit_nat_like_family_baseline` | pass | pass |
| `admit_prop_family_with_sort1_field` | pass | pass |
| `prop_exemption_is_sound_because_large_elimination_is_denied` | pass | pass |
| `positivity_prepass_precedes_the_universe_check` | pass | pass |

Baseline `--lib inductive`: **56 passed, 0 failed** (49 before ADR-1500's split
of one test into eight).

Three of the new ones earn their place by reaching something the original
could not:

- **`_polymorphic`** refuses at a universe PARAMETER rather than a literal:
  `Box.{u} : Sort u` with `mk : Sort u → Box.{u}`, whose field type inhabits
  `Sort (u+1)`. It exercises `level_leq` on a non-literal level, which the
  `Sort 1` case cannot; a guard comparing only numerals would pass the literal
  test and admit this one.
- **`admit_nat_like_family_baseline`** pins that `level_leq` must hold at
  EQUALITY. `N : Sort 1` with `succ : N → N` has a field at exactly the
  family's own universe, so a guard written `<` instead of `≤` would refuse
  every recursive family in the eleven preludes.
- **`admit_bundled_sort2_structure_with_sort1_carrier`** is `AbsProbe.Field`
  in miniature — a `Sort 2` family whose first field is a `Sort 1` carrier and
  whose later fields are typed *through* it — which reaches the case of a field
  domain mentioning an earlier field's fvar. The full 17-field probe in
  `examples/bundled_structure_probe.rs` covers the same ground but is an
  example, so nothing runs it.

## Finding 1 — nothing checked that `Prop`'s exemption is SOUND

The guard exempts `Prop` because it is impredicative. Presence of the exemption
is not an argument for it. `P : Prop` with `mk : Sort 1 → P` stores a `Sort 1`
in exactly the way the refused `SelfU` does; large elimination is the second
half of the Girard construction, and if such a family had it, the exemption
would be the hole rather than the fix.

It does not, and the reason is a **separate mechanism in a different function**:

```rust
let allows_large_elimination = self.level_is_nonzero(group.result_level)
    || (group.families.len() == 1
        && match group.families[0].constructors.as_slice() {
            [] => true,
            [constructor] => constructor.exposes_non_prop_fields,
            _ => false,
        });
```

A `Prop` family whose single constructor exposes a non-proof field is denied
large elimination, so its motive is `Prop`-valued and no `Sort 1` can be
recovered. **Nothing in the workspace connected the exemption to the mechanism
that makes it safe.** `prop_exemption_is_sound_because_large_elimination_is_denied`
now asserts that such a family's recursor carries no elimination universe
parameter — with a fieldless `True`-like `Prop` singleton, which DOES get large
elimination, as the non-vacuity control. Without that partner the test would
pass on a kernel that denied large elimination to every `Prop` family, which is
a different and wrong kernel.

This is the blind spot mutation testing cannot cover, in its exact documented
form: mutation deletes guards that exist. The connection between two correct
mechanisms is not a guard, so there was nothing to delete and nothing to
survive.

## Finding 2 — the check order is the reverse of what the tree says

`reject_ctor_wrong_param`'s doc comment states that "the two checks run in
Lean's order (universe per field, result at the end)". A test asserting the
analogous claim against POSITIVITY was written here and **the kernel refuted
it**: for `BadBoth : Sort 1` with

```
mk : Sort 1 → (BadBoth → BadBoth) → BadBoth
```

— illegal twice over, with the universe-illegal field at index 0 and the
non-positive field at index 1 — the reported error is
`NonPositiveInductiveOccurrence { field_index: 1 }`.

The cause is structural, not incidental: `check_group_constructor_positivity`
is a **whole separate pre-pass over every constructor**, run before the
`check_group_ctor` loop that carries the universe check. So positivity precedes
the universe constraint for all fields, not merely for an earlier-indexed one.

Nothing is unsound about one refusal masking another — both refuse. It is
recorded because it decides the expected verdict for any generated case that is
both universe-illegal and non-positive, which is precisely the interaction the
next section turns on. `positivity_prepass_precedes_the_universe_check` pins it,
and is labelled an ordering control rather than a guard pin because it passes in
both configurations.

## Decision

1. **The universe guard is pinned by named controls in both directions**, and
   the with/without result is stated per control rather than per suite. Two
   tests die without it; six pass with and without it.

2. **Registered in `scripts/tests/mutation_controls.py` as
   `inductive-universe-guard`**, with two mutations that fail in opposite
   directions and are killed by disjoint test sets:

   | mutation | killed |
   | --- | --- |
   | guard made dead (`false && …`) | 2 tests |
   | `Prop` exemption dropped (`if true`) | 6 tests |

   The harness does cover Rust — its `Cargo` runner goes through
   `scripts/cargo-serialized.sh test` — so this needs no new machinery, and a
   future lane re-runs the whole measurement with
   `python3 scripts/tests/mutation_controls.py inductive-universe-guard`.

3. **Restoring illegal coverage to the grammar generators is follow-on, not
   this lane.** The generators once emitted 360 Lean-illegal cases asserting
   ADMIT and now emit none; neither is right, and a generator producing both
   shapes with the correct verdict for each is what would have caught this
   originally. It is deferred rather than declined because two costs are real
   and neither is the axis itself:

   - `mutual_inductive_group_grammar` pins a byte-exact
     `EXPECTED_GENERATED_SUMMARY` including an fnv1a64 digest over every
     descriptor. Adding a third `FamilySort` (`Sort 1` alongside `Prop` and
     `Sort 2`) takes 360 cases to 540 and forces that digest to be
     regenerated — in the same commit that changes it, which is the
     "editing a file that pins its own digest" failure this repository has
     already paid for. A restoration needs the digest regenerated in a
     commit that changes nothing else.
   - Finding 2 makes the axes non-independent. A case that is both
     universe-illegal and a negative production rejects with the POSITIVITY
     error, so `expected_error` becomes order-dependent. That is worth
     pinning and is more than an enum arm.

   The design, so the follow-on lane does not re-derive it: the sort axis
   becomes `{Prop, Sort1, Sort2}`; every generated field domain is `Sort 1`,
   so the expected verdict is derivable — refuse with
   `ConstructorFieldUniverseTooBig` iff the family's result universe is
   neither `Prop` nor `≥ Sort 2`, and defer to the positivity error when the
   production is negative. The `Prop`/`Type` split must be part of the
   generated grammar, not bolted on beside it.

## Consequences

- The three suites named in ADR-1495 remain unable to detect the guard's
  removal. That is now a recorded fact with a decision attached rather than an
  unmeasured assumption.
- `--lib inductive` is the workspace's only detector, which makes it a
  pre-merge gate for any change to `inductive.rs` — and it is cheap
  (0.2 s at 56 tests).
- The general rule this instance supports, and the reason it is worth an ADR
  rather than a commit message: **when a fix repairs a fixture that was
  asserting the bug, the repaired fixture is the least likely thing to detect a
  regression.** It has been moved to the legal side of the boundary. The
  mutation target must be chosen from what the guard REFUSES, not from what the
  fix touched.

## Alternatives considered

- **Leave the bundled test as it was.** Rejected: it pins the guard, so it is
  not wrong, but it cannot answer the over-refusal question in the run where
  that question is asked, and over-refusal in `add_inductive` breaks all
  eleven preludes at once.
- **Assert the `Prop` exemption by declaring `Exists` and `Acc`.** Rejected as
  the primary control: it shows the exemption is *needed*, not that it is
  *safe*. The large-elimination denial is what makes it safe and is what is
  now asserted.
- **Restore illegal grammar coverage in this lane.** Rejected for the two
  costs above; recorded as follow-on with a design rather than as a wish.

## References

- [ADR-1495](adr-1495-abstraction-over-structures-is-already-expressible-the-gap-is-surface.md)
  — the fix, and the probe whose universe control did not fire.
- `crates/axeyum-lean-kernel/src/inductive.rs` — the guard and the
  `allows_large_elimination` mechanism that makes `Prop`'s exemption sound.
- `crates/axeyum-lean-kernel/src/inductive/inductive_tests.rs` — the eight
  controls.
- `scripts/tests/mutation_controls.py` — suite `inductive-universe-guard`.
