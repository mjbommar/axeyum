#!/usr/bin/env python3
"""Controls for `analyze.py`'s STRUCTURE test.

Two groups, one checked-in fixture (`fixtures/synthetic_structure.tsv`,
generated once through `outcome_ledger.LedgerRow`/`to_line` so its bytes are
real wire-format rows, not hand-typed TSV):

* `SYN/Int`  -- 10 rows. `fast-route` decides 8 of 10 (80% >= the 70% floor),
  but `slow-route` is the first-attempted route on EVERY row (including the
  two `slow-route` deciders). MUST report STRUCTURE, with `reorder_rows == 8`
  (the fast-route deciders, whose first-attempted route was not the decider)
  and `ceiling_ms == 4000` (8 rows x the 500 ms `slow-route` spent first on
  each before `fast-route` decided in 50 ms).

* `SYN/Real` -- 10 rows, one route (`only-route`), both first-attempted and
  sole decider on every row. A reorder of a one-route class changes nothing
  by construction. MUST report NO STRUCTURE (the positive control the brief
  asks for: a class where the answer is obviously "no", confirmed by the
  same code path that answers the real divisions), with `reorder_rows == 0`
  and `ceiling_ms == 0`.

Exit status is the finding: 0 only if both assertions hold.
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "scripts"))

import outcome_ledger as ol  # noqa: E402
from analyze import analyze_group, build_groups  # noqa: E402

FIXTURE = HERE / "fixtures" / "synthetic_structure.tsv"


def main() -> int:
    rows = ol.read_ledger(FIXTURE)
    assert len(rows) == 20, f"fixture row count moved: {len(rows)}"

    groups = build_groups(rows)
    assert ("SYN", "Int") in groups, sorted(groups)
    assert ("SYN", "Real") in groups, sorted(groups)

    struct_result = analyze_group(groups[("SYN", "Int")], min_decided=5, top_share=0.70)
    single_result = analyze_group(groups[("SYN", "Real")], min_decided=5, top_share=0.70)

    failures = []

    if not struct_result["structure"]:
        failures.append(f"SYN/Int: expected STRUCTURE, got {struct_result}")
    if struct_result["top_decider"] != "fast-route":
        failures.append(f"SYN/Int: expected top_decider=fast-route, got {struct_result['top_decider']}")
    if struct_result["reorder_rows"] != 8:
        failures.append(f"SYN/Int: expected reorder_rows=8, got {struct_result['reorder_rows']}")
    if struct_result["ceiling_ms"] != 4000:
        failures.append(f"SYN/Int: expected ceiling_ms=4000, got {struct_result['ceiling_ms']}")
    if struct_result["prefix_cost_ms"] != 4000:
        failures.append(f"SYN/Int: expected prefix_cost_ms=4000, got {struct_result['prefix_cost_ms']}")
    if struct_result["prefix_cost_files"] != 8:
        failures.append(f"SYN/Int: expected prefix_cost_files=8, got {struct_result['prefix_cost_files']}")

    if single_result["structure"]:
        failures.append(f"SYN/Real: expected NO STRUCTURE, got {single_result}")
    if single_result["reorder_rows"] != 0:
        failures.append(f"SYN/Real: expected reorder_rows=0, got {single_result['reorder_rows']}")
    if single_result["ceiling_ms"] != 0:
        failures.append(f"SYN/Real: expected ceiling_ms=0, got {single_result['ceiling_ms']}")
    if single_result["prefix_cost_ms"] != 0:
        failures.append(f"SYN/Real: expected prefix_cost_ms=0, got {single_result['prefix_cost_ms']}")

    if failures:
        for f in failures:
            print(f"FAIL: {f}", file=sys.stderr)
        return 1

    print("OK: SYN/Int -> STRUCTURE (top_decider=fast-route 8/10, reorder_rows=8, ceiling_ms=4000)")
    print("OK: SYN/Real -> NO STRUCTURE (single-route class, reorder_rows=0, ceiling_ms=0)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
