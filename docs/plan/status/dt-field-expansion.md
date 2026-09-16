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

**Mutation: both guards kill EXACTLY ONE test, and they are DIFFERENT tests**
(`census/mutation-dt-nested-field-2128.txt`, baseline green at 8 tests):

| guard deleted | the test that died |
|---|---|
| the materialiser skips a CYCLIC field closure | `the_cyclic_guard_builds_no_children_for_a_cyclic_datatype` |
| the exactness predicate recurses into the nested field | `exactness_widens_with_the_budget_and_never_for_a_cycle` |

**And the first mutant for guard 2 was not usable**, which is the more useful
half of the result. Deleting the `depth > 0 &&` conjunct reported
`INCONSISTENT — 1 test binaries started but 0 reported a result`: without the
budget check the predicate DIVERGES on a cyclic datatype and takes the binary
down. A crash is a kill in the crudest sense and it NAMES NOTHING, so it is not
a result. The registered mutant keeps the budget and drops the RECURSION
instead (`depth > 0 && ..._to_depth(inner, depth - 1)` → `depth > 0`), which
terminates and is wrong: a datatype-typed field counts as exact whenever any
budget remains, so a cyclic closure is called exact — the ADR-1920
antecedent-weakening shape.

**The lever IS live end to end, and the verdict column cannot show it.**
ADR-2114's own `repro/ground.smt2` answers `unsat` through the FRONT DOOR under
BOTH arms — a lower rung (ADR-0022 step A) decides it after
`check_with_datatype_native` declines — so it cannot confirm the arm is
enabled. A real `dt:exactness-arg` corpus file can
(`census/lever-endtoend-probe.txt`): BASE gives up on "congruence over a
datatype argument whose expansion is not exact", ARM at depth 5 gives up on an
unrelated `(Uninterpreted 6)` sort the BV backend cannot bit-blast. **The
exactness refusal is gone under the arm and the verdict is `unknown` under
both** — the lever MOVES THE BLOCKER without moving the verdict here.

**THE A/B IS COMPLETE AND THE HELD-OUT DRAW REVERSES IT.**

Pinned lists (the set this lane measured on), one binary, two env values, arms
back to back per file on one core, order alternated, 24 s, pinned pairs on s7:

| division | base | arm | gains | losses | flips |
|---|---|---|---:|---:|---:|
| `AUFDTLIRA` | unsat 119, unk 81 | unsat 122, unk 78 | 3 | 0 | 0 |
| `UFDTLIRA` | unsat 138, unk 56, sat 6 | unsat 139, unk 55, sat 6 | 1 | 0 | 0 |
| `QF_DT` | unsat 107, unk 29, sat 64 | identical | 0 | 0 | 0 |
| **total (600)** | | | **4** | **0** | **0** |

Held-out draw, 200 fresh files per moving division (seeded, pools of 10,843 and
7,549, pinned + ledger paths excluded and the exclusion checked at 0 leaked):

| division | base | arm | gains | losses | flips |
|---|---|---|---:|---:|---:|
| `AUFDTLIRA`-heldout | unsat 134, unk 66 | unsat 133, unk 67 | 1 | **2** | 0 |
| `UFDTLIRA`-heldout | unsat 132, unk 68 | unsat 134, unk 66 | 2 | 0 | 0 |

All nine movers and both losses rechecked **3x per arm** plus `z3 -T:60` and
`:status`. **Both losses are STABLE 3 of 3.** 0 flips across all 1,000 A/B rows
— the lever never produced a wrong verdict, only fewer verdicts on files it had
not been measured on.

**SHIP DECISION: DO NOT SHIP.** The criterion (0 stable losses, 0 flips, >=1
stable gain, on the pinned list AND the held-out draw) is not met. The lever
stays OFF and ADR-2128 stays `proposed`. The pinned 600 would have shipped on
its own numbers; the held-out draw is the only reason it does not.

**Why it costs as well as pays — one mechanism seen twice.** On the loss
`N624-020__perm_rem__perm.adb_252_25_precondition` the base is
`decided_by=q:mbqi-quick` in 1,736 ms and the arm hits the watchdog at 24 s; on
the gain `O512-022__stacks` the base hits the watchdog and the arm decides in
337 ms. The nested expansion changes the ground closure inside the quantifier
loop in both strength and cost, and nothing measured here predicts which side a
file falls on — **`CLEAN` in particular does not**. A follow-up needs a COST
model, not more coverage.

**Gates.**

| gate | result |
|---|---|
| dispatch/reason block (whole hook list) | 23 suites, 219 tests, 0 failed, 0 inert |
| `progress_frontier` | 12 tests, 0 failed, no REGRESSION; pins restored, `git status` 0 dirty |
| lib sweep `--skip reconstruct::` | 1579 passed, 1 failed — **PRE-EXISTING** |
| `config_registry::tests` | 18 green |
| 12 DT suites | 113 tests green, nonzero counts |
| mutation `dt-nested-field-2128` | 2 guards, each killing exactly one DIFFERENT test |
| `--check-anchors` | `suites=150 anchors=1100 stale=0` |
| `check-merge-hygiene.sh` / `check-links.sh` | PASS / all links ok |
| workspace `--all-targets --all-features` clippy | **NOT RUNNABLE HERE** — `z3-static` pulls `z3-sys`, whose build script downloads the `z3-4.16.0` release asset; a fresh worktree target dir has no cached copy. Run by the coordinator on the merged tree. The narrower `-p axeyum-solver -p axeyum-bench --all-targets --features full` is clean, and is **not the same gate**. |

The lib-sweep failure is `auto::tests::pathological_overbound_stays_terminal_under_every_policy`
in `auto.rs`, a file this lane does not touch. **Measured, not asserted:** the
same sweep on a `lane-snapshot.sh` tree of the merge base (confirmed to lack
`datatype_expansion_is_exact_to_depth` before being trusted) fails that test
**and** `arithmetic_uf_overbound_pre_lia_probe_decides_on_clone` — 2 failures on
the base against 1 here.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `09d03cc2e` | `expansion-reach.py` + the seven-population reach census, with three committed controls (fires on ADR-2114's own `ground.smt2`, not on either negative). |
| 2026-09-16 | `cb60fb9ba` | ADR-2128: nested datatype field expansion behind `AXEYUM_DT_NESTED_FIELD_DEPTH` (default 0 = OFF); depth-aware exactness, cyclic-closure detector, demand-seeded materialiser, 16 tests, a new pre-push-gated suite. |
| 2026-09-16 | `9fe46e8c3` | The observed blocker census (318 undecided files, 0 unmatched sentences), clippy clean, and the `dt-nested-field-2128` mutation suite. |
| 2026-09-16 | `35b27b5ed` | The pinned A/B, all three divisions: 600 files, 4 gains, 0 losses, 0 flips; the seeded held-out draw. |
| 2026-09-16 | `70c50a703` | ADR-2128 §5, the lane status, and a mutant replaced because it CRASHED rather than failed. |
| 2026-09-16 | `2943e88c2` | The end-to-end lever probe (the arm clears the exactness refusal on a real corpus file) and `ab-summarize.py`, whose exit status depends on the finding. |
