# Lane: dt-array-element — the refused sort is exactly what the brief said, and it blocks 2 rows of 800

<!-- plan-section: lane-status -->

**Lane dt-array-element (`DONE`, dt-array-element, 2026-09-16).** Three lanes
narrowed the datatype side of `AUFDTLIRA` to one refusal: `register_datatype`
refuses the first non-expanding sort in a datatype's field closure. This lane
was dispatched to admit that sort — an array whose element is a datatype — as an
opaque container.

**The sizing confirms the premise about WHICH sort and refutes the premise about
HOW MUCH.** `(Array Int <datatype>)` is 142 of 142 refused sorts on the ground
probe's 83 files, 112 of 112 on `AUFDTLIRA`'s undecided files, 86 of 86 and 112
of 112 on ADR-2114's two populations — **zero** are an array with an
uninterpreted domain or range, which is a different site. But only **2 of 81**
undecided `AUFDTLIRA` rows TERMINATE at the refusal; the other 10 of the 12
files that carry a refused datatype die at `quant:ematching` (6) or the ADR-2103
quant-route decline (4). `UFDTLIRA` is **0 of 56** and `QF_DT` is **0 of 29** at
either measure.

ADR: [ADR-2135](../../research/09-decisions/adr-2135-arrays-of-datatypes-as-opaque-elements.md)
· artifact: [`bench-results/dt-array-element-20260916/`](../../../bench-results/dt-array-element-20260916/README.md)

## What landed — one predicate, behind an OFF lever

`field_is_opaque` is the single definition of "opaque field", used by the three
sites that must agree (ADR-1920's lockstep rule): `register_datatype` admits on
it, `build_sym_vars` skips on it, `scan_fragment` refuses a `select` of it. With
the lever OFF it is `matches!(sort, Sort::Datatype(_))` — the pre-ADR-2135
predicate — so the shipped behaviour is unchanged.

An opaque field gets NO expansion variable, so `datatype_expansion_is_exact`
stays false for the owning datatype: no congruence is emitted over it and
`build_dt_eq` keeps the free-boolean relaxed form. Traversal is refused twice
over — the new `scan_fragment` arm, and the UNCHANGED
`refuse_if_datatype_survives`. Neither guard is weakened; what the lever lifts is
the refusal that fires on the DECLARATION, before any traversal is known about.

| what | where |
|---|---|
| `field_is_opaque`, `dt_has_opaque_field`, `DT_ARRAY_ELEMENT_DEFAULT`, `DatatypeArrayElementGuard`, `AXEYUM_DT_ARRAY_ELEMENT` | `crates/axeyum-solver/src/datatype_native.rs` |
| `DT_ARRAY_ELEMENT_DEFAULT` registry entry, dated to the artifact, with `note_crossed` wired | `crates/axeyum-solver/src/config_registry.rs` |
| 12-test suite: both lever arms, both verdict directions, the traversal decline, the ADR-1930 wrong-`unsat` pair, a nested-element control | `crates/axeyum-solver/tests/dt_array_element_2135.rs` |
| suite registration, default arm and `AXEYUM_DT_ARRAY_ELEMENT=on` armed arm | `hooks/pre-push` |
| `dt-array-element-2135`: 2 mutations, 2 killed, exactly 1 named test each | `scripts/tests/mutation_controls.py` |
| sizing, lists, A/B scripts and every capture | `bench-results/dt-array-element-20260916/` |

## What this lane did NOT build, and what it would cost

The lever opens a DECLARATION, not a traversal. A `select` of the opaque field
is a decline, so SPARK's `(select (rec__content r) i)` — the shape the two
terminal files actually have — is not reached. Reaching it needs the array's own
sort-abstraction route (ADR-2065's `OpaqueReals` shape: abstract the
array-of-datatype to an array over a fresh uninterpreted sort, over-approximate,
replay every `sat`), because the residual otherwise carries an array-of-datatype
term and `datatype_native.rs`'s own `solve(arena, &reduced, config)` re-dispatch
routes it straight back — the ADR-1920 cycle, measured as a stack overflow with
a 1 GiB stack. That is a real build, and at 2 rows of 800 it is not the next
thing to spend on.

<!-- plan-section: landed-changes -->

| 2026-09-16 | dt-array-element | **Sizing first, and it is the finding.** The sort `register_datatype` refuses is `(Array Int <datatype>)` on **142/142**, **112/112**, **86/86** and **112/112** of four measured populations — the premise is exactly right, and **zero** refused sorts are an array with an uninterpreted domain or range (a different site, `auto.rs`, 4 of 81 `AUFDTLIRA` rows). But the refusal is the TERMINAL reason on only **2 of 81** undecided `AUFDTLIRA` rows, **0 of 56** `UFDTLIRA` and **0 of 29** `QF_DT`; the 12 `AUFDTLIRA` files that declare a refused datatype mostly die at `quant:ematching` or the ADR-2103 quant-route decline instead. Ceiling **6 of 800** across the four A/B divisions. Built anyway, behind an OFF lever, as the narrow SOUND slice: `field_is_opaque` — one predicate for the three sites ADR-1920 requires to agree — admits an array-of-datatype FIELD as an opaque container with no expansion variable, so the exactness predicate and the relaxed `build_dt_eq` regime are untouched and traversal is refused twice over. 12 tests, 2 mutations killing exactly one named fixture each, `--check-anchors` stale=0. The traversing half — SPARK's actual shape — needs the array's sort-abstraction route (ADR-2065's `OpaqueReals`), because the residual otherwise re-enters `datatype_native` through its own `solve` call and that is the ADR-1920 stack-overflow cycle; ADR-2135 |
