#!/usr/bin/env python3
"""Catalog-only proposer for a tiny, target-independent Nat induction grammar.

The proposer does not parse proof bodies or decide whether a plan is valid.  It
enumerates the same bounded structural plans for every target binder.  A fresh
kernel process validates the binder sort, executes the plan, and decides
whether the resulting term has the registered target type.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys
from typing import Any


BASE = "definitional-reflexivity"
STEPS = ("exact-induction-hypothesis", "successor-congruence-induction-hypothesis")


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def build_bundle(catalog: dict[str, Any]) -> dict[str, Any]:
    if catalog.get("proof_bodies_included") is not False:
        raise ValueError("catalog does not explicitly exclude proof bodies")
    arity = catalog["target"]["arity"]
    if not isinstance(arity, int) or isinstance(arity, bool) or arity < 1:
        raise ValueError("target arity must be a positive integer")
    plans = []
    for binder in range(arity):
        for step in STEPS:
            plans.append(
                {
                    "rank": len(plans) + 1,
                    "operation": "induct-nat",
                    "target_binder": binder,
                    "base": BASE,
                    "step": step,
                }
            )
    bundle: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-induction-proposals",
        "catalog_sha256": catalog["catalog_sha256"],
        "phase": catalog["phase"],
        "target": catalog["target"],
        "policy": "binder-order-then-structural-step",
        "plans": plans,
    }
    bundle["bundle_sha256"] = digest(bundle)
    return bundle


def render_tsv(bundle: dict[str, Any]) -> str:
    rows = [
        "AXEYUM_INDUCTION_PLANS_V1"
        f"\t{bundle['bundle_sha256']}\t{bundle['catalog_sha256']}\t{bundle['phase']}"
    ]
    rows.extend(
        f"{plan['rank']}\t{plan['target_binder']}\t{plan['base']}\t{plan['step']}"
        for plan in bundle["plans"]
    )
    return "\n".join(rows) + "\n"


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: autogenesis-induction-proposer.py CATALOG OUTPUT_DIR", file=sys.stderr)
        return 2
    catalog = json.loads(pathlib.Path(sys.argv[1]).read_text())
    output = pathlib.Path(sys.argv[2])
    bundle = build_bundle(catalog)
    (output / "induction-plans.json").write_text(
        json.dumps(bundle, indent=2, sort_keys=True) + "\n"
    )
    (output / "induction-plans.tsv").write_text(render_tsv(bundle))
    print(
        f"AUTOGENESIS_INDUCTION_PROPOSALS|phase={bundle['phase']}|"
        f"plans={len(bundle['plans'])}|bundle={bundle['bundle_sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
