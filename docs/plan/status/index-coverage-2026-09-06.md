# Lane: index-coverage — the retrieval index must see the whole kernel

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, index-coverage, 2026-09-06).** `shape_search`
built 17 of the crate's 31 `pub fn build_*_prelude` functions and returned
nothing for `--ns FO` against a 4,839-row dump; it now builds all 31 plus all 9
exported non-prelude builders, from ONE table, gated from outside by a census
whose subject is read from `src/` on every run. The same audit over all 45
kernel instruments is a script with a two-sided ratchet. ADR-1672 records the
rule and every measurement. All four deliverables landed.

## Commits

| SHA | what |
|---|---|
| `ab65eb262` | the census test, committed RED on purpose |
| `64805f48c` | `shape_search` builds the whole kernel, from one `GROUPS` table |
| `c324e1044` | fix: the census counted call sites, not `GROUPS` rows (found by RUNNING the mutants) |
| `33043aaa0` | the two census gates get disjoint denominators |
| `d6410a981` | sibling instruments declare coverage; `scripts/audit-kernel-tool-prelude-coverage.py` |
| `9d1899d1d` | fix: the ratchet could not see a small tool losing its coverage line (found by RUNNING M7) |
| `1dea2a565` | ADR-1672 and the two contributor guides |

## The measurement that put this here, and what it is now

| | before | after |
|---|---|---|
| `pub fn build_*_prelude` reached | 17 / 31 | **31 / 31** |
| exported non-prelude builders reached | 2 / 9 | **9 / 9** |
| default `coverage:` groups | 8 | 15 |
| `--include-constructed` groups | 16 | 25 |
| `--ns FO` | 0 rows against a 4,839-row dump | **141** |
| `List` namespace | 15 | **31** (`List.Perm` resolves, `FOUND 1`) |
| `AxReal` namespace | 30 | **74** |
| `--name-contains Metric.prod` | ABSENT | **FOUND 10** |
| default declarations | 3,340 | 3,558 |
| constructed declarations | 4,839 | 5,091 |

The example's own internal cross-check passed the whole time, because both
halves were hand-written and omitted the same builders. **A check whose two
sides are written by one hand at one moment cannot fail.** That is the general
lesson; the group list being "derived" saved nothing, because a comparison is
worth what its most independent side is worth.

## Cost, measured interleaved on one box, load beside every number

| index | before | after |
|---|---|---|
| default | 26.7 s (load 16.8), 19.1 s (load 30.3) | 58.0 s (load 20.5), 52.2 s (load 29.8) |
| constructed | 167.1 s (load 25.8), 183.0 s (load 12.1) | 235.6 s (load 12.6), 303.4 s (load 21.3) |

Per group, default index (53.1 s total, load 17.8 → 15.4):

    logic=0.0s nat=4.8s axreal=0.0s integer=3.2s rat=13.1s ipc=0.2s
    ipc_eval=0.1s fo_order=0.8s fo_soundness=0.4s fo_substitution=0.3s
    characterization=0.3s list=5.2s int_model=7.6s rat_model=14.4s string=2.3s

**The FO groups — the largest blind spot — are the cheapest thing added:**
1.5 s for all three leaves and all eleven builders. `int_model` (7.6 s) and
`rat_model` (14.4 s) are what tripled the default index.

They stay in the default anyway, and the reason is a soundness property of the
flag rather than a preference: `--include-constructed` is safe only because an
unbuilt group's namespace is absent ENTIRELY, so a query comes back
`UNANSWERABLE` (exit 3) rather than ABSENT. The models declare into
`AxReal.IntModel`/`AxReal.RatModel` and `namespace_root` is the first segment,
so `AxReal` is in the index either way — gating them would produce a confident
wrong ABSENT for `AxReal.IntModel.add_comm`. **A group may go behind a flag
only if its whole namespace root goes with it.**

## Mutation table — RUN, not predicted

Census suite (`tests/shape_search_index_coverage.rs`), against a snapshot at
`33043aaa0`. Baseline 4 tests, 4 passed, nothing dying.

| mutant | predicted | actually died | verdict |
|---|---|---|---|
| M1 delete the `metric_prod` `Group` row | `…every_prelude_builder` | `…every_prelude_builder` | MATCH |
| M2 delete the `fo_substitution` `Group` row | `…every_prelude_builder` | `…every_prelude_builder` | MATCH |
| M3 drop `build_list_perm` from the `list` group | `…every_exported_non_prelude_builder` | same | MATCH |
| M4 rename `GROUPS` (re-split into two lists) | `…derives_its_groups_from_one_table` | same | MATCH |
| M5 allowlist a real gap with an EMPTY reason | `reasons_are_measured` | same | MATCH |
| M6 allowlist a builder that does not exist | `reasons_are_measured` | same | MATCH |

Exactly one test dies per mutant.

**Two of these did not match on the first run, and that is the finding.**

* **M1 and M2 originally survived: 4 tests, NOTHING died.** `shape_search_direct`
  scanned the WHOLE example for call sites, and deleting a `Group` row leaves
  the helper `fn build_metric_prod` in the file as dead code still containing
  the call. The census could be satisfied by a function nothing would ever run —
  the defect it was written to catch, one level up. Fixed in `c324e1044`: the
  walk now starts at the `build:` fields.
* **M1/M2 then killed TWO tests each**, because the wide gate's denominator was
  a superset of the narrow one's. Split into disjoint denominators in
  `33043aaa0`.

Audit ratchet (`scripts/audit-kernel-tool-prelude-coverage.py`), against a
snapshot at `9d1899d1d`. Baseline exit 0.

| mutant | predicted exit | run exit | verdict |
|---|---|---|---|
| M7 delete `nat_theorem_inventory`'s coverage line | 1 | 1 | MATCH |
| M8 add a coverage line to `structural_index_extract` | 1 | 1 | MATCH |
| M9 raise `COVERAGE_THRESHOLD` to 999 (population empties) | 1 | 1 | MATCH |
| M10 break the builder-name regex (authority finds nothing) | 1 | 1 | MATCH |

**M7 originally survived with exit 0.** The threshold rule ("build ≥ 3 preludes,
declare coverage") protected the thirteen tools I did not fix and not one of the
four I did: `nat_theorem_inventory` builds one prelude and never enters the
counted population. `PIN_DECLARING` (`9d1899d1d`) closes it. M9 and M10 are the
gate's own liveness controls — it must not pass by examining nothing, and must
abort rather than report zero when its authority scan is broken.

## Tool × preludes-built, all 45 instruments

`python3 scripts/audit-kernel-tool-prelude-coverage.py [--blind] [--check]`

| instrument | preludes (of 31) | declares coverage |
|---|---|---|
| `shape_search` | 31 | yes |
| `kernel_declaration_projection` | 17 | no |
| `prelude_theorem_inventory` | 13 | **yes (new)** |
| `theorem_dependency_inventory` | 10 | **yes (new)** |
| `footprint_closure_audit` | 9 (6 default) | **yes (new)** |
| `kernel_stack_envelope`, `nat_axiom_inventory`, `prelude_axiom_inventory`, `structural_index_extract` | 9 | no |
| `fo_order_inventory` | 8 | no |
| `fo_robinson_inventory`, `prelude_build_timing` | 7 | no |
| `fo_code_inventory` | 6 | no |
| `fo_soundness_inventory` | 5 | no |
| `ipc_soundness_inventory`, `metric_prod_theorem_inventory` | 4 | no |
| `theorem_axiom_footprint` | 3 | no |
| `nat_theorem_inventory` | 1 | **yes (new)** |
| 27 further single-subject probes | 1–2 | no |

Before this lane: 16 of the 17 at-threshold instruments declared nothing. Now
13, pinned two-sided.

## Gates run, with counts and exit status

| gate | result |
|---|---|
| `cargo test -p axeyum-lean-kernel --release --test shape_search_index_coverage` | **4 tests, 4 passed, 0 failed** (nonzero count confirmed) |
| `scripts/check-clippy-complete.sh` | **807 of 807 workspace targets across 27 of 27 crates, 0 diagnostics**, exit 0 |
| `cargo build --release -p axeyum-lean-kernel --examples` | clean, 0 warnings |
| `rustfmt --edition 2024 --check` on all 8 touched Rust files | clean |
| `python3 scripts/audit-kernel-tool-prelude-coverage.py --check` | 45 / 17 / 13 (pin 13); 5 declaring (pin 5); **exit 0** |
| `./scripts/check-links.sh` | `all links ok`, exit 0 |
| `python3 scripts/gen-adr-index.py` | 884 rows regenerated |

## What did NOT land, with the measured obstruction

* **The remaining 13 instruments do not print a coverage line.** Held by the
  ratchet, not fixed. Each is a one-line edit; the obstruction is only that
  fixing them requires knowing what each one actually builds and stating it
  correctly, and a wrong coverage line is worse than none. The audit script
  prints every one of them by name on every run.
* **Three `pub fn build_*` helpers are covered by neither gate**:
  `build_add_le_add_left`, `build_distrib_r`, `build_mul_one_l`. They are not
  exported from `lib.rs`, so no example can call them. They declare into
  preludes that ARE covered, so nothing they produce is missing from the index —
  but the census cannot prove that, and the ADR says so rather than implying it.
* **Hiding place 2 is untouched.** An inline step inside a larger declaration
  has no declaration, so no index over declared names can list it. This lane
  did not change that and nothing here should be read as having done so.

## Explicitly did NOT run

* `just check` / `./scripts/check.sh` — the aggregate gates. Not run.
* `cargo test --workspace` in any form. Only the one new integration suite was
  run; the rest of the kernel suite was not.
* `cargo test -p axeyum-lean-kernel --release` (the whole crate's tests).
  Not run — this lane touched only `examples/`, `tests/` and docs, but that is
  an argument, not a measurement.
* `python3 scripts/validate-facts.py`, `just foundational-resources`,
  `scripts/check-merge-hygiene.sh`, `python3 scripts/gen-plan.py`. Not run.
* No push. No merge to `main`.
