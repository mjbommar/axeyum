# Lane: py-fields-registries — the Python prelude-field table and the gate that keeps it current

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, py-fields-registries, 2026-09-01).** Opened. Two
defects from the `creal-split-2` registry move are in scope: the 62 moved
`CRealPrelude` fields are absent from the generated Python table
(`crates/axeyum-py/src/kernel/prelude_fields.rs`), and
`scripts/gen-py-prelude-fields.py --check` is registered in no gate, which is
why the stale generated file reached main. Work: make the generator
registry-aware (dotted names), wire `--check` into
`scripts/check-merge-hygiene.sh` and `scripts/check.sh` with a
mutation-verified control, and give `scripts/creal-migrate-registry.py` a
workspace-wide consumer scan that refuses on external flat readers.

<!-- plan-section: landed-changes -->

| 2026-09-01 | py-fields-registries | lane opened; status stub |
