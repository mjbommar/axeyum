#!/usr/bin/env python3
"""Generate `artifacts/structural-index/*` (L3 phase D2, ADR-0905).

This script does NOT run cargo. It reads the already-produced
`theorems.json` (produced by the Rust extractor below) and derives every
other committed artifact from it plus the already-committed fact ledger and
nursery files -- the same "gen script trusts a committed input, check script
re-derives everything from committed inputs" split
`check-declaration-graph.py` documents for its own gate ("the checker needs
no Lean toolchain... it validates the committed graph").

To (re)produce `theorems.json`:

    cargo run --release -p axeyum-lean-kernel --example structural_index_extract \\
      -- > artifacts/structural-index/theorems.json

`--include-constructed` may be added to that command to also cover
`creal`/`complex`/`cpoint`; this phase's committed artifact does NOT pass it
(cost/benefit: the fixed queries below do not need those declarations, and
building them adds real kernel type-checking time to every regeneration).

Usage:

    python3 scripts/gen-structural-index.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import structural_index as si  # noqa: E402

OUT_DIR = si.INDEX_DIR
THEOREMS_PATH = OUT_DIR / "theorems.json"

# The fixed queries this phase's exit criterion asks for: "fixed queries
# reproduce exact ranked candidates". Expected names are computed below by
# actually running the query engine against the committed `theorems.json`
# at generation time, then committed verbatim -- a future regeneration that
# changes the answer must be reviewed, not silently accepted.
FIXED_QUERIES = [
    {
        "id": "cross-namespace-shared-machinery",
        "description": (
            "Both Int.prodRange_permute and Nat.countRange_permute directly "
            "reference Nat.restrict_injective and Nat.restrict_maps_into, "
            "even though they live in different namespaces and have "
            "different conclusion heads (AxInt.prodRange vs AxNat.countRange "
            "in export form) -- the case "
            "docs/plan/definition-discovery-efficiency-roadmap-2026-08-30.md "
            "D2 names as unreachable by shape_search's --concl/--hyp query."
        ),
        "query": {
            "kind": "dependency",
            "has_dependencies": [
                "Nat.restrict_injective",
                "Nat.restrict_maps_into",
            ],
        },
    },
    {
        "id": "pigeonhole-consumers",
        "description": (
            "Every direct consumer of the pigeonhole lemma "
            "Nat.injective_on_imp_surjective_on, across both the Nat and "
            "Int namespaces."
        ),
        "query": {
            "kind": "dependency",
            "has_dependencies": ["Nat.injective_on_imp_surjective_on"],
        },
    },
    {
        "id": "identity-miss-on-plausible-guess",
        "description": (
            "An EXACT-name guess at the natural snake_case spelling of "
            "Nat.crtSelfMap_injectiveOn is ABSENT under identity, precisely "
            "because the kernel name is camelCase-in-part. Paired with the "
            "lexical query below to demonstrate the two columns disagree."
        ),
        "query": {"kind": "identity", "name": "Nat.crt_self_map_injective_on"},
    },
    {
        "id": "lexical-hit-on-same-guess",
        "description": (
            "The SAME snake_case guess as the query above, asked as a "
            "spelling-insensitive LEXICAL query, finds the declaration the "
            "identity query above could not."
        ),
        "query": {"kind": "lexical", "name_like": "crt_self_map_injective_on"},
    },
]

# A query that must be UNANSWERABLE, not a silent empty match -- one of the
# dependency names does not exist anywhere in the index's vocabulary.
UNANSWERABLE_QUERY = {
    "id": "unknown-dependency-is-unanswerable",
    "description": (
        "One of the two named dependencies does not exist anywhere in the "
        "index; this must be reported UNANSWERABLE, never a silent empty "
        "AND-match, so an absent name cannot be confused with a genuine "
        "zero-result query."
    ),
    "query": {
        "kind": "dependency",
        "has_dependencies": [
            "Nat.restrict_injective",
            "Nat.this_declaration_does_not_exist",
        ],
    },
}


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    if not THEOREMS_PATH.exists():
        print(
            f"gen-structural-index: {THEOREMS_PATH} does not exist -- run "
            "the cargo extractor first (see this file's module docstring)",
            file=sys.stderr,
        )
        return 1
    records = si.load_theorems(THEOREMS_PATH)
    if not records:
        print("gen-structural-index: theorems.json is empty", file=sys.stderr)
        return 1
    dep_index = si.build_dependency_index(records)

    # Held-out exclusion + Mathlib goal-feature join.
    features, manifest = si.build_mathlib_goal_features()
    (OUT_DIR / "mathlib-goal-features.json").write_text(
        json.dumps(features, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (OUT_DIR / "held-out-exclusion-manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    # Fixed queries with committed expected rankings.
    queries_out = []
    for spec in FIXED_QUERIES:
        rows = si.run_query(records, dep_index, spec["query"])
        queries_out.append(
            {
                "id": spec["id"],
                "description": spec["description"],
                "query": spec["query"],
                "expected_names": sorted(r["name"] for r in rows),
                "expected_rows": sorted(rows, key=lambda r: r["name"]),
            }
        )
    try:
        si.run_query(records, dep_index, UNANSWERABLE_QUERY["query"])
        print(
            "gen-structural-index: UNANSWERABLE_QUERY unexpectedly answered",
            file=sys.stderr,
        )
        return 1
    except si.Unanswerable:
        pass
    queries_out.append(
        {
            "id": UNANSWERABLE_QUERY["id"],
            "description": UNANSWERABLE_QUERY["description"],
            "query": UNANSWERABLE_QUERY["query"],
            "expect_unanswerable": True,
        }
    )
    (OUT_DIR / "queries.json").write_text(
        json.dumps(queries_out, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    print(
        "GEN_STRUCTURAL_INDEX|records="
        f"{len(records)}|goal_features={len(features)}|"
        f"held_out_excluded={manifest['held_out_excluded_count']}|"
        f"queries={len(queries_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
