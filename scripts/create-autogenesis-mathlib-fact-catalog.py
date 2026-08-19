#!/usr/bin/env python3
"""Materialize reviewed Mathlib statements as open, proof-isolated fact rows."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
REVIEW = ROOT / "artifacts/autogenesis/mathlib-nat-int-reviewed-nursery-v1.json"
COMPONENTS = ROOT / "artifacts/autogenesis/mathlib-nat-int-dependency-components-v1.json"
CATALOG = ROOT / "artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json"
FACTS = ROOT / "artifacts/facts"
SOURCE_COMMIT = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
SOURCE_TAG = "v4.30.0"
SURFACE_ATTESTATION_SHA256 = "a4f51828c0b70709aeef3429400d8fac90f80d5d3164bd8259b1b5fd1fd5995d"
SURFACE_NORMALIZATIONS = {
    "Nat.choose_mono": "∀ (b : ℕ), Monotone (fun a : ℕ => a.choose b)",
    "Nat.clog_antitone_left": "∀ {n : ℕ}, AntitoneOn (fun b : ℕ => Nat.clog b n) (Set.Ioi 1)",
    "Nat.fib_add_two_strictMono": "StrictMono (fun n : ℕ => Nat.fib (n + 2))",
    "Nat.log_antitone_left": "∀ {n : ℕ}, AntitoneOn (fun b : ℕ => Nat.log b n) (Set.Ioi 1)",
}


class CatalogError(RuntimeError):
    """The reviewed source cannot be projected to an honest fact catalog."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load_object(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise CatalogError(f"{path} is not a JSON object")
    return value


def verified_digest(value: dict[str, Any], field: str, label: str) -> None:
    unsigned = dict(value)
    claimed = unsigned.pop(field, None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise CatalogError(f"{label} digest is missing or invalid")


def slug(value: str) -> str:
    rendered = re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")
    return rendered or "statement"


def source_fact_id(row: dict[str, Any]) -> str:
    return f"F:ml430-{slug(row['name'])}-{row['candidate_id'][:8]}"


def mutation_fact_id(row: dict[str, Any]) -> str:
    return f"F:ml430-mutation-{row['mutation_id'].removeprefix('M:').lower()}"


def statement_shape(statement: str) -> str:
    if "∃" in statement:
        return "existential-witness"
    if statement.startswith("¬"):
        return "negated-proposition"
    if any(marker in statement for marker in ("Monotone", "StrictMono", "Antitone", "Symmetric", "Function.swap")):
        return "higher-order-property"
    if re.search(r"\{?f\s*:\s*Bool\s*→", statement):
        return "higher-order-property"
    if "↔" in statement:
        return "biconditional"
    if "→" in statement:
        return "conditional-proposition"
    if "=" in statement:
        return "unconditional-equality"
    return "unconditional-relation"


def surface_statement(name: str, statement: str) -> str:
    """Restore only binder annotations lost by standalone pretty printing."""
    return SURFACE_NORMALIZATIONS.get(name, statement)


def lean_surface_module(review: dict[str, Any]) -> str:
    statements: list[tuple[str, str]] = []
    for row in review["reviewed_candidates"]:
        if row["disposition"] == "evaluation-eligible":
            statements.append((source_fact_id(row), surface_statement(row["name"], row["statement"])))
    for row in review["mutations"]:
        statements.append((mutation_fact_id(row), row["statement"]))
    lines = [
        "import Mathlib",
        "",
        "/- Generated proof-free syntax/type validation for Axeyum nursery statements. -/",
        "namespace AxeyumAutogenesisSurface",
        "",
    ]
    for fact_id, statement in sorted(statements):
        name = "s_" + fact_id.removeprefix("F:").replace("-", "_")
        lines.extend((f"axiom {name} :", f"  ({statement})", ""))
    lines.extend(("end AxeyumAutogenesisSurface", ""))
    return "\n".join(lines)


def build(review: dict[str, Any], components: dict[str, Any]) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    verified_digest(review, "review_sha256", "review")
    verified_digest(components, "components_sha256", "dependency component")
    if review.get("state") != "reviewed-groups-not-frozen-split":
        raise CatalogError("review source state is invalid")
    if review.get("dependency_components_sha256") != components.get("components_sha256"):
        raise CatalogError("review and dependency components differ")

    eligible = {
        row["name"]: row
        for row in review.get("reviewed_candidates", [])
        if row.get("disposition") == "evaluation-eligible"
    }
    if len(eligible) != review.get("coverage", {}).get("evaluation_eligible_candidates"):
        raise CatalogError("eligible review count is stale")
    if not set(SURFACE_NORMALIZATIONS).issubset(eligible):
        raise CatalogError("surface normalization names a non-eligible statement")
    fact_id_by_name = {name: source_fact_id(row) for name, row in eligible.items()}
    if len(set(fact_id_by_name.values())) != len(fact_id_by_name):
        raise CatalogError("source fact ids collide")

    direct_dependencies: dict[str, list[str]] = {name: [] for name in eligible}
    for component in components.get("components", []):
        for edge in component.get("edges", []):
            dependent = edge["dependent"]
            dependency = edge["dependency"]
            if dependent in eligible and dependency in eligible:
                direct_dependencies[dependent].append(dependency)
    for name in direct_dependencies:
        direct_dependencies[name] = sorted(set(direct_dependencies[name]))

    facts: dict[str, dict[str, Any]] = {}
    catalog_rows: list[dict[str, Any]] = []
    for name in sorted(eligible):
        row = eligible[name]
        fact_id = fact_id_by_name[name]
        formal_statement = surface_statement(name, row["statement"])
        fact = {
            "schema_version": 1,
            "id": fact_id,
            "title": f"Mathlib v4.30 source proposition {name}",
            "statement": f"The proposition declared as `{name}` in the pinned Mathlib v4.30 source.",
            "formal": {
                "language": "lean4-surface",
                "statement": formal_statement,
                "fragment": row["domain"],
            },
            "epistemic_status": "open",
            "external_status": "proved",
            "depends_on": [fact_id_by_name[dependency] for dependency in direct_dependencies[name]],
            "evidence": [],
            "provenance": {
                "date": "2026-08-18",
                "established_by": "not established in this ledger",
                "source": f"statement-only extraction of `{name}` from Mathlib {SOURCE_TAG}; no proof value was exposed",
                "prior_art": [
                    {
                        "who": "the Mathlib contributors",
                        "what": f"the theorem declaration `{name}`",
                        "where": f"mathlib4 commit {SOURCE_COMMIT} ({SOURCE_TAG})",
                        "year": 2026,
                        "attribution": "the proposition was read from the pinned statement-only inventory; the proof term and tactic trace were not consulted",
                    }
                ],
            },
            "notes": "Open in Axeyum. The external theorem declaration is prior art, not a locally constructed proof. formal.statement is Lean surface syntax accepted as a proposition by the proof-free generated axiom module; it is not kernel-core render_lean output. depends_on projects only direct upstream theorem uses whose endpoints both survived review. Those edges are curriculum and leakage metadata and grant no dispatch, proof, or admission authority.",
        }
        facts[fact_id] = fact
        catalog_rows.append(
            {
                "dependency_component_id": row["dependency_component_id"],
                "direct_dependency_fact_ids": fact["depends_on"],
                "fact_id": fact_id,
                "family": row["theme"],
                "kind": "external-source",
                "source_name": name,
                "source_statement_sha256": hashlib.sha256(row["statement"].encode()).hexdigest(),
                "statement_shape": statement_shape(formal_statement),
                "surface_normalization": "explicit-lambda-binder" if formal_statement != row["statement"] else "identity",
            }
        )

    mutation_ids: set[str] = set()
    for row in review.get("mutations", []):
        source_id = fact_id_by_name.get(row["source_name"])
        if source_id is None:
            raise CatalogError(f"mutation source {row['source_name']} is not eligible")
        fact_id = mutation_fact_id(row)
        if fact_id in facts or fact_id in mutation_ids:
            raise CatalogError("mutation fact ids collide")
        mutation_ids.add(fact_id)
        fact = {
            "schema_version": 1,
            "id": fact_id,
            "title": f"Outcome-blind mutation of {row['source_name']}",
            "statement": f"A `{row['mutation_class']}` mutation of the pinned source proposition `{row['source_name']}`.",
            "formal": {
                "language": "lean4-surface",
                "statement": row["statement"],
                "fragment": row["domain"],
            },
            "epistemic_status": "open",
            "external_status": "unknown",
            "depends_on": [],
            "evidence": [],
            "provenance": {
                "date": "2026-08-18",
                "established_by": "not established in this ledger",
                "source": f"outcome-blind `{row['mutation_class']}` mutation of {row['source_name']}",
            },
            "notes": "Open generated mutation. No expected truth value, proof, witness, route, budget, or Axeyum outcome is recorded. formal.statement is Lean surface syntax accepted as a proposition by the proof-free generated axiom module. The nursery manifest, not depends_on, keeps this row in the same partition as its source.",
        }
        facts[fact_id] = fact
        catalog_rows.append(
            {
                "dependency_component_id": row["dependency_component_id"],
                "direct_dependency_fact_ids": [],
                "fact_id": fact_id,
                "family": row["theme"],
                "kind": "generated-mutation",
                "mutation_class": row["mutation_class"],
                "mutation_of_fact_id": source_id,
                "source_name": row["source_name"],
                "statement_shape": statement_shape(row["statement"]),
            }
        )

    catalog_rows.sort(key=lambda row: row["fact_id"])
    shape_counts = Counter(row["statement_shape"] for row in catalog_rows)
    surface_sha256 = hashlib.sha256(lean_surface_module(review).encode()).hexdigest()
    if surface_sha256 != SURFACE_ATTESTATION_SHA256:
        raise CatalogError("generated surface module changed without a new real-Lean attestation")
    catalog: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-mathlib-open-fact-catalog",
        "state": "open-facts-no-splits-no-outcomes",
        "review_sha256": review["review_sha256"],
        "dependency_components_sha256": components["components_sha256"],
        "source": {"mathlib_commit": SOURCE_COMMIT, "mathlib_tag": SOURCE_TAG, "lean_version": "4.30.0"},
        "surface_validation": {
            "method": "declare every formal.statement as an axiom after import Mathlib; no theorem value or proof is read",
            "generated_module_sha256": surface_sha256,
            "expected_sha256": SURFACE_ATTESTATION_SHA256,
            "statement_count": len(catalog_rows),
            "external_file": "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-nat-int-nursery-surface-v1.lean",
            "bytes": 22670,
            "mode": "0444",
            "command": "cd <mathlib-v4.30.0-checkout> && lake env lean <external_file>",
            "observed_result": "accepted-214-proof-free-axiom-types",
        },
        "coverage": {
            "facts": len(catalog_rows),
            "external_sources": len(eligible),
            "generated_mutations": len(mutation_ids),
            "families": len({row["family"] for row in catalog_rows}),
            "statement_shape_counts": dict(sorted(shape_counts.items())),
        },
        "facts": catalog_rows,
        "limitations": [
            "Lean surface propositions are not Axeyum kernel-core terms",
            "real-Lean proposition acceptance is syntax/type evidence, not proof evidence",
            "Mathlib declarations remain external prior art and every Axeyum fact remains open",
            "direct source dependencies are curriculum metadata and do not grant admission credit",
            "partitions and route hypotheses remain unassigned",
        ],
    }
    catalog["catalog_sha256"] = digest(catalog)
    return catalog, facts


def fact_path(fact_id: str) -> pathlib.Path:
    return FACTS / (fact_id.replace("F:", "F-") + ".json")


def write_outputs(catalog: dict[str, Any], facts: dict[str, dict[str, Any]]) -> None:
    CATALOG.write_text(json.dumps(catalog, indent=2, sort_keys=True) + "\n")
    for fact_id, fact in sorted(facts.items()):
        path = fact_path(fact_id)
        if path.exists():
            raise CatalogError(f"refusing to overwrite existing fact {path.relative_to(ROOT)}")
        path.write_text(json.dumps(fact, indent=2, ensure_ascii=False) + "\n")


def verify_catalog(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    verified_digest(actual, "catalog_sha256", "fact catalog")
    if actual != expected:
        raise CatalogError("committed fact catalog is stale or mutated")
    if actual.get("state") != "open-facts-no-splits-no-outcomes":
        raise CatalogError("fact catalog falsely claims a split or outcome")
    fact_ids = [row.get("fact_id") for row in actual.get("facts", [])]
    if fact_ids != sorted(fact_ids) or len(fact_ids) != len(set(fact_ids)):
        raise CatalogError("catalog fact ids are duplicate or out of order")


def verify_outputs(catalog: dict[str, Any], facts: dict[str, dict[str, Any]]) -> None:
    actual = load_object(CATALOG)
    verify_catalog(actual, catalog)
    for fact_id, expected in facts.items():
        path = fact_path(fact_id)
        if not path.is_file() or load_object(path) != expected:
            raise CatalogError(f"fact {fact_id} is absent, stale, or mutated")
    catalog_ids = {row["fact_id"] for row in catalog["facts"]}
    if catalog_ids != set(facts):
        raise CatalogError("fact catalog and generated fact set differ")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--emit-lean", type=pathlib.Path)
    args = parser.parse_args()
    if sum((args.check, args.write, args.emit_lean is not None)) != 1:
        parser.error("choose exactly one of --check, --write, or --emit-lean")
    try:
        review = load_object(REVIEW)
        components = load_object(COMPONENTS)
        if args.emit_lean is not None:
            args.emit_lean.write_text(lean_surface_module(review))
            print(f"AUTOGENESIS_MATHLIB_SURFACE_EMIT|{args.emit_lean}|sha256={hashlib.sha256(args.emit_lean.read_bytes()).hexdigest()}")
            return 0
        catalog, facts = build(review, components)
        if args.write:
            write_outputs(catalog, facts)
        else:
            verify_outputs(catalog, facts)
        print(
            "AUTOGENESIS_MATHLIB_FACT_CATALOG_OK|"
            f"{catalog['catalog_sha256']}|facts={catalog['coverage']['facts']}|"
            f"sources={catalog['coverage']['external_sources']}|mutations={catalog['coverage']['generated_mutations']}"
        )
    except (OSError, json.JSONDecodeError, CatalogError) as error:
        print(f"autogenesis-mathlib-fact-catalog: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
