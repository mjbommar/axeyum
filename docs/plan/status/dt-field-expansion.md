# Lane: dt-field-expansion — ADR-2128, nested datatype field expansion

<!-- plan-section: lane-status -->

**The lever's two preconditions are ANTI-CORRELATED across the DT divisions,
and the site DT-GROUND-PROBE named is not the one the representation reaches**
(`IN PROGRESS`, dt-field-expansion, 2026-09-16,
`bench-results/dt-field-expansion-20260916/`, ADR-2128).

[ADR-2114] §4 named recursive tag/field expansion of a datatype-typed field as
the repair for the `INEXACT` datatype bucket; DT-GROUND-PROBE put **8 of 14**
undecided files at `register_datatype` (`datatype_native.rs:1511-1518`) and
pointed this lane at that representation. **Sizing first found the two lanes
name two different sites.**

`register_datatype` already WALKS INTO a `Sort::Datatype` field (`:1508-1511`);
its refusal fires on the first non-datatype, non-expanding sort in the closure,
which on the probe's own bucket is `(Array Int <datatype>)` on **8 of 8** files
and **142 of 142** refused sorts across that population. Depth unrolling reaches
none of it — which [ADR-2114] §4 says in its own words about the `W1` arm. And
where the target bucket IS the blocker, `QF_DT`, the field closure is CYCLIC on
**29 of 29** undecided files, so no finite unrolling of them is exact.

What the lever DOES reach is the **Ackermann exactness precondition**, not the
`==` encoding: `expand_datatype_equalities` already compares one nesting level
and `unfold_traversals` already gives it children, so a free-variable `a != b`
is decided with the lever OFF. Traced at 24 s on s7 pinned cores, the **318
undecided files** of the four DT divisions bucket as:

| terminal site | n | CLEAN |
|---|---:|---:|
| `quant:ematching` | 101 | 26 |
| `quant:watchdog` | 53 | 38 |
| **`dt:exactness-result` (`:904`)** | **40** | 4 |
| `quant:time-budget` | 31 | 21 |
| **`dt:relaxation-incomplete`** | **29** | 0 |
| `quant:instantiation-sat` | 14 | 0 |
| **`dt:exactness-arg` (`:963`)** | **12** | 6 |
| `backend:sort-mismatch` | 7 | 7 |
| `bv:datatype-sorted-term` | 7 | 4 |
| `dt:ack-pair-bound` | 6 | 6 |
| `dt:model-lacks-field` | 5 | 1 |
| `quant:mbqi-unsupported` | 4 | 4 |
| `dt:field-sort-W1` | 2 | 0 |
| `quant:mbqi-rounds` | 1 | 0 |

0 unmatched sentences. The three ADR-2128 buckets are **81 of 318 (25.5 %)**;
`CLEAN` (a convertible datatype AND no cyclic and no `W1`-refused datatype in
the same file) is **10 of those 81**, and is a LOWER bound — 23 undecided rows
have no reach row because the file declares no datatype at all.

Shipped behind `AXEYUM_DT_NESTED_FIELD_DEPTH`, **default 0 = OFF**
(`cb60fb9ba`, 7 files): one depth-aware `datatype_expansion_is_exact_to_depth`
whose `k == 0` is the pre-change predicate verbatim and which terminates on its
own decreasing budget; `datatype_field_closure_is_cyclic` (following MUTUAL
cycles); `materialize_nested_children`, seeded from the EQUALITY SITES as both
references are (cvc5 `theory_datatypes.cpp:1932-1948`, z3
`theory_datatype.cpp:432-436`) and reusing `unfold_traversals`'s child NAMES so
a slot that is both traversed and compared is one child; `nested_child_eq`
recursing on a budget one smaller. 16 tests (8 in a new pre-push-gated suite
`dt_nested_field_2128`, 8 unit), 12 DT suites green at 113 tests,
`config_registry::tests` 18 green with two new dated/undated entries plus
`MAX_ACK_PAIRS`, unregistered since [ADR-1935].

**The observed census, which the shape census could not give.** Traced all 318
undecided files with `--trace` at 24 s on s7 pinned cores and bucketed the
give-up sentence by the code site it NAMES (substring of the raw detail, never
a label). The three ADR-2128 buckets are **81 of 318 (25.5 %)**, `CLEAN` is
**10 of those 81**, and `dt:relaxation-incomplete` (29) — `project_and_replay`
throwing away a `sat` candidate because the traversed-field children are FREE —
sits entirely in files that are cyclic or `W1`-blocked. 0 unmatched sentences.

**Gates.** `clippy -p axeyum-solver -p axeyum-bench --all-targets --features
full -- -D warnings` clean (the five findings were cleared by extracting
`field_conjunct`, `child_slot`, `ctor_field_agreement` and
`insert_eq_replacements` — `field_conjunct` is a real improvement, because both
`==` encodings now decide which slots they can see in ONE place). Default
features `cargo check -p axeyum-solver` exit 0. `check-merge-hygiene.sh` PASS.
`check-links.sh` all links ok. `mutation_controls.py --check-anchors`
`suites=150 anchors=1100 stale=0`.

**Mutation, and the first mutant was not usable.** Guard 1 (the materialiser
skips a cyclic closure) killed **exactly one** test,
`the_cyclic_guard_builds_no_children_for_a_cyclic_datatype` — which is the
design: the guard moves the child COUNT and nothing else, so a verdict
assertion would have survived it. Guard 2's obvious mutant — deleting
`depth > 0 &&` — reported `INCONSISTENT — 1 test binaries started but 0
reported a result`: without the budget check the predicate DIVERGES on a cyclic
datatype and takes the binary down. A crash names nothing, so the registered
mutant keeps the budget and drops the RECURSION instead, which terminates and
is wrong.

**Ship decision: NOT TAKEN — the interleaved A/B did not complete in this
lane.** The lever stays OFF, which is what it ships as. The runner
(`ab-run.sh`, one binary two env values, arms back to back per file on one
core, order alternated per file) and the three 200-file lists are committed, so
the measurement is a re-run rather than a re-derivation.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `09d03cc2e` | `expansion-reach.py` + the seven-population reach census, with three committed controls (fires on ADR-2114's own `ground.smt2`, not on either negative). |
| 2026-09-16 | `cb60fb9ba` | ADR-2128: nested datatype field expansion behind `AXEYUM_DT_NESTED_FIELD_DEPTH` (default 0 = OFF); depth-aware exactness, cyclic-closure detector, demand-seeded materialiser, 16 tests, a new pre-push-gated suite. |
| 2026-09-16 | `9fe46e8c3` | The observed blocker census (318 undecided files, 0 unmatched sentences), clippy clean, and the `dt-nested-field-2128` mutation suite. |
