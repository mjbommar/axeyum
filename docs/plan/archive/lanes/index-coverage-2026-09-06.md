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
| `cc32bbd7a` | per-group `timing:` line; clippy `-D warnings`; close-out |
| `4fd4fe16b` | `kernel_declaration_projection` builds every prelude — **check-trust-closure 23 failures → 2** |
| `580517fba` | the three `AxReal.*Model` groups come back out, with the measurement |
| `27f94a39a` | regenerate `artifacts/autogenesis/kernel-dependency-projection-v1.json` |

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
| default declarations | 3,340 | 3,514 |
| constructed declarations | 4,839 | 5,025 |

### The strongest result is downstream, and it is not "we found more things"

`examples/kernel_declaration_projection.rs` had the same gap and
`scripts/check-trust-closure.py` reads its environment, so that gate was RED on
main with 21 SUBJECT-ABSENT rows — 16 `FO.*`, 4 `Top.*`, 1 `Metric.*`, exactly
the namespaces the example omitted. Every one of those subjects exists, proved,
in the tree.

| `check-trust-closure.py` | before (main `29953abe1`) | after |
|---|---|---|
| declarations | 4,817 | 5,023 |
| subjects | 2,503 | 2,524 |
| `absent` | **21** | **0** |
| `guard population` rejected | 21 | 0 |
| failures | 23 | 2 |

**A tool with partial coverage does not merely fail to find things. It
manufactures findings in every gate built on top of it, and nothing downstream
can tell those from real ones.** The two remaining failures are a different
class: `alias_occurrence rejected=1` was in the baseline, and
`IDENTITY-MAP-DRIFT` is the script's deliberate review event for a changed
identity map. Neither was auto-updated.

### And an over-reach of mine, caught by running the gates rather than reasoning

I added the three `AxReal.*Model` groups beyond the brief. `check-merge-hygiene.sh`
PASSED on `29953abe1` and FAILED on my branch in two places, both mine:
`check-shape-duplicates.py` exit 2 (85 duplicate groups against a 40-line
limit, **66 of them a model law beside its own carrier law**) and the
kernel-projection staleness (4,817 vs 5,091, tolerance 100). A model law is by
construction a restatement of the law it interprets, so those 66 are noise in
the gate whose job is finding re-derivations. The three are now allowlisted
with that measurement as their reason, and the cost regression went with them.

The example's own internal cross-check passed the whole time, because both
halves were hand-written and omitted the same builders. **A check whose two
sides are written by one hand at one moment cannot fail.** That is the general
lesson; the group list being "derived" saved nothing, because a comparison is
worth what its most independent side is worth.

## Cost, measured interleaved on one box, load beside every number

| index | before | after |
|---|---|---|
| default | 26.7 s (load 16.8), 19.1 s (load 30.3) | **23.2 s** (load 12.5) |
| constructed | 167.1 s (load 25.8), 183.0 s (load 12.1) | **181.4 s** (load 12.5) |

The intermediate state that carried the three model groups ran 58.0 s / 52.2 s
default and 235.6 s / 303.4 s constructed — that is the "roughly tripled" figure
the earlier commits report, and it is gone.

Per group, default index (23.2 s total, load 12.5):

    logic=0.0s nat=4.0s axreal=0.0s integer=3.0s rat=9.3s ipc=0.1s
    ipc_eval=0.1s fo_order=0.4s fo_soundness=0.2s fo_substitution=0.1s
    characterization=0.2s list=3.4s string=2.2s

**The FO groups — the largest blind spot — are the cheapest thing here: 0.7 s
for all three leaves and all eleven builders.** The default index carries 174
more declarations than the baseline at the baseline's cost.

The rule that survived the model episode, for the next lane: **a group may go
behind `--include-constructed` only if its whole namespace root goes with it.**
That flag is safe only because an unbuilt group's namespace is absent ENTIRELY,
so a query returns `UNANSWERABLE` (exit 3) rather than ABSENT. A group sharing a
namespace root with an indexed group cannot be gated without manufacturing a
confident wrong ABSENT — which is why the models were removed outright and
allowlisted rather than moved behind the flag.

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

A seventh, unplanned mutant arrived by accident and is worth recording: the
over-broad edit that removed the three model groups also swallowed
`build_creal`, `build_complex`, `build_cpoint`, `build_metric` and
`build_metric_prod`, leaving five `GROUPS` rows pointing at deleted functions.
The census caught it — `BLIND (2): build_complex_prelude
build_metric_prod_prelude` — before any build did.

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
| `cargo test -p axeyum-lean-kernel --release --test shape_search_index_coverage` | **5 tests, 5 passed, 0 failed** (nonzero count confirmed) |
| `scripts/check-clippy-complete.sh` | **807 of 807 workspace targets across 27 of 27 crates, 0 diagnostics**, exit 0 |
| `cargo build --release -p axeyum-lean-kernel --examples` | clean, 0 warnings |
| `rustfmt --edition 2024 --check` on all 8 touched Rust files | clean |
| `python3 scripts/audit-kernel-tool-prelude-coverage.py --check` | 45 / 17 / 13 (pin 13); 5 declaring (pin 5); **exit 0** |
| `./scripts/check-links.sh` | `all links ok`, exit 0 |
| `scripts/check-merge-hygiene.sh` | **PASS** — and it FAILED twice mid-lane on defects this lane introduced; both fixed |
| `python3 scripts/check-shape-duplicates.py --prebuilt` | 20 groups, all allowlisted, exit 0 (was exit 2 mid-lane at 85) |
| `python3 scripts/check-trust-closure.py` | **failures 23 → 2**, `absent` 21 → 0 |
| `python3 scripts/gen-autogenesis-kernel-dependency-projection.py` | regenerated, 5,023 declarations / 3,384 theorems / 20,084 edges |
| `python3 scripts/gen-plan.py` | 637 lanes, regenerated |
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
* **`check-trust-closure.py` still has 2 failures**, both diagnosed and
  neither this class: `guard alias_occurrence rejected=1` was in the baseline,
  and `IDENTITY-MAP-DRIFT` is the script's own review event for a changed
  identity map. I did NOT run it with `--update`: the script says a new or
  vanished equivalence class is a review event, and accepting one silently to
  make a gate green is the defect this lane spent its day on.
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
* `python3 scripts/validate-facts.py` and `just foundational-resources`.
  Not run.
* No push. No merge to `main`.
