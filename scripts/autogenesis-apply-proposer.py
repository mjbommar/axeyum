#!/usr/bin/env python3
"""Catalog-only proposer: enumerate same-arity theorem applications.

The sandbox runner invokes this with exactly two arguments: the verified
catalog path and an empty output directory.  It deliberately performs no proof
checking.  It proposes a deterministic finite set; the separate kernel checker
decides whether any proposal proves the target.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def build_bundle(catalog: dict[str, Any]) -> dict[str, Any]:
    if catalog.get("proof_bodies_included") is not False:
        raise ValueError("catalog does not explicitly exclude proof bodies")
    target_arity = catalog["target"]["arity"]
    eligible = [entry for entry in catalog["entries"] if entry["arity"] == target_arity]
    eligible.sort(key=lambda entry: (entry["origin"] != "accepted-episode", entry["name"]))
    plans = [
        {
            "rank": rank,
            "operation": "apply-visible-theorem",
            "theorem": entry["name"],
            "arguments": [{"target_binder": index} for index in range(target_arity)],
            "catalog_origin": entry["origin"],
        }
        for rank, entry in enumerate(eligible, start=1)
    ]
    bundle: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-apply-proposals",
        "catalog_sha256": catalog["catalog_sha256"],
        "phase": catalog["phase"],
        "target": catalog["target"],
        "policy": "accepted-episode-first-then-name",
        "plans": plans,
    }
    bundle["bundle_sha256"] = digest(bundle)
    return bundle


def render_tsv(bundle: dict[str, Any]) -> str:
    tsv = [
        "AXEYUM_APPLY_PLANS_V1"
        f"\t{bundle['bundle_sha256']}\t{bundle['catalog_sha256']}\t{bundle['phase']}"
    ]
    tsv.extend(
        f"{plan['rank']}\t{plan['theorem']}\t{len(plan['arguments'])}"
        for plan in bundle["plans"]
    )
    return "\n".join(tsv) + "\n"


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: autogenesis-apply-proposer.py CATALOG OUTPUT_DIR", file=sys.stderr)
        return 2
    catalog = json.loads(pathlib.Path(sys.argv[1]).read_text())
    output = pathlib.Path(sys.argv[2])
    bundle = build_bundle(catalog)
    (output / "apply-plans.json").write_text(
        json.dumps(bundle, indent=2, sort_keys=True) + "\n"
    )
    (output / "apply-plans.tsv").write_text(render_tsv(bundle))
    print(
        f"AUTOGENESIS_APPLY_PROPOSALS|phase={bundle['phase']}|plans={len(bundle['plans'])}|"
        f"bundle={bundle['bundle_sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
