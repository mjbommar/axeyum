#!/usr/bin/env python3
"""Generate an evidence-backed Axeyum product-health snapshot.

This is intentionally a *static* snapshot.  It measures committed populations
and whether the canonical aggregate gates reach their authorities.  It does not
claim that CI, ``just check``, or any individual gate ran successfully at the
commit: runtime results need their own authenticated execution record.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import Counter
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
EPISODES = ROOT / "artifacts/episodes"
PROJECTION = ROOT / "artifacts/autogenesis/kernel-dependency-projection-v1.json"
LEMMA_INDEX = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-v1.json"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
OUTCOMES = ROOT / "artifacts/autogenesis/producer-outcome-observations-v1.json"
CONCEPT_COVERAGE = ROOT / "artifacts/autogenesis/concept-coverage-projection-v1.json"
JUSTFILE = ROOT / "justfile"
SHELL_GATE = ROOT / "scripts/check.sh"
JSON_OUT = ROOT / "artifacts/product-health-v1.json"
MARKDOWN_OUT = ROOT / "docs/plan/generated/product-health.md"


class HealthError(RuntimeError):
    """The snapshot cannot be derived honestly from the committed sources."""


def _load(path: pathlib.Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise HealthError(f"cannot read {path.relative_to(ROOT)}: {error}") from error
    if not isinstance(value, dict):
        raise HealthError(f"{path.relative_to(ROOT)} is not a JSON object")
    return value


def _sha256(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _relative(path: pathlib.Path) -> str:
    return path.relative_to(ROOT).as_posix()


def _population_sha256(paths: list[pathlib.Path]) -> str:
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(_relative(path).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def _facts() -> dict[str, Any]:
    statuses: Counter[str] = Counter()
    routes: Counter[str] = Counter()
    count = 0
    for path in sorted(FACTS.glob("F-*.json")):
        fact = _load(path)
        count += 1
        status = fact.get("epistemic_status")
        if not isinstance(status, str):
            raise HealthError(f"{_relative(path)} has no epistemic_status")
        statuses[status] += 1
        route = fact.get("proof_route")
        if isinstance(route, str):
            routes[route] += 1
    return {
        "facts": count,
        "status_counts": dict(sorted(statuses.items())),
        "proof_route_counts": dict(sorted(routes.items())),
    }


def _episodes() -> dict[str, Any]:
    verdicts: Counter[str] = Counter()
    schema_versions: Counter[str] = Counter()
    paths = [
        path
        for path in sorted(EPISODES.rglob("*.json"))
        if not any(part.startswith("fixtures") for part in path.parts)
    ]
    for path in paths:
        episode = _load(path)
        outcome = episode.get("outcome")
        verdict = outcome.get("verdict") if isinstance(outcome, dict) else None
        if not isinstance(verdict, str):
            raise HealthError(f"{_relative(path)} has no verdict")
        verdicts[verdict] += 1
        schema_versions[str(episode.get("schema_version"))] += 1
    if not paths:
        raise HealthError("production episode population is empty")
    return {
        "production_episodes": len(paths),
        "fixture_episodes_excluded": len(list(EPISODES.glob("fixtures*/*.json"))),
        "verdict_counts": dict(sorted(verdicts.items())),
        "schema_version_counts": dict(sorted(schema_versions.items())),
    }


def _operations(document: dict[str, Any]) -> dict[str, Any]:
    rows = document.get("operations")
    if not isinstance(rows, list):
        raise HealthError("operation registry has no operations array")
    authoritative = [row for row in rows if row.get("scope") == "authoritative"]
    multi_target = []
    named_facts: set[str] = set()
    for row in authoritative:
        applicability = row.get("applicability")
        fact_ids = applicability.get("fact_ids") if isinstance(applicability, dict) else None
        if not isinstance(fact_ids, list) or not all(isinstance(item, str) for item in fact_ids):
            raise HealthError(f"operation {row.get('id')!r} has no typed fact_ids")
        named_facts.update(fact_ids)
        if len(fact_ids) > 1:
            multi_target.append({"id": row.get("id"), "fact_count": len(fact_ids)})
    return {
        "registered_operations": len(rows),
        "authoritative_operations": len(authoritative),
        "authoritative_named_facts": len(named_facts),
        "reusable_multi_target_operations": sorted(multi_target, key=lambda row: str(row["id"])),
    }


def _gate_wiring() -> dict[str, Any]:
    just = JUSTFILE.read_text()
    shell = SHELL_GATE.read_text()
    check_line = next((line for line in just.splitlines() if line.startswith("check:")), "")
    just_dependencies = set(check_line.removeprefix("check:").split())
    required = {
        "python_authority": (
            "py-check" in just_dependencies,
            "step py-pytest" in shell and "step py-types" in shell,
        ),
        "production_episodes": (
            "episodes" in just_dependencies and "--production-only" in just,
            "step episodes" in shell and "--production-only" in shell,
        ),
        "kernel_projection": (
            "autogenesis-kernel-projection" in just_dependencies,
            "step autogenesis-kernel-projection" in shell,
        ),
        "semantic_coverage": (
            "autogenesis-concept-coverage" in just_dependencies,
            "step autogenesis-concept-coverage" in shell,
        ),
    }
    return {
        name: {"just_check": just_ok, "shell_fallback": shell_ok, "both": just_ok and shell_ok}
        for name, (just_ok, shell_ok) in required.items()
    }


def build() -> dict[str, Any]:
    projection = _load(PROJECTION)
    lemma_index = _load(LEMMA_INDEX)
    operations = _load(OPERATIONS)
    outcomes = _load(OUTCOMES)
    concept_coverage = _load(CONCEPT_COVERAGE)
    projection_census = projection.get("census")
    lemma_census = lemma_index.get("census")
    outcome_census = outcomes.get("census")
    concept_census = concept_coverage.get("census")
    if not all(
        isinstance(row, dict)
        for row in (projection_census, lemma_census, outcome_census, concept_census)
    ):
        raise HealthError("one or more generated authorities have no census object")

    sources = [
        PROJECTION,
        LEMMA_INDEX,
        OPERATIONS,
        OUTCOMES,
        CONCEPT_COVERAGE,
        JUSTFILE,
        SHELL_GATE,
    ]
    fact_paths = sorted(FACTS.glob("F-*.json"))
    production_episode_paths = [
        path
        for path in sorted(EPISODES.rglob("*.json"))
        if not any(part.startswith("fixtures") for part in path.parts)
    ]
    return {
        "schema_version": 1,
        "kind": "axeyum-product-health-snapshot",
        "scope": "committed-populations-and-static-gate-reachability",
        "runtime_gate_status": {
            "state": "not-recorded",
            "meaning": "This artifact does not claim that just check, CI, or any constituent gate ran successfully.",
        },
        "kernel_library": projection_census,
        "knowledge_connectivity": lemma_census,
        "semantic_coverage": concept_census,
        "fact_ledger": _facts(),
        "autonomous_production": {
            **_operations(operations),
            "production_episodes": _episodes(),
            "producer_outcome_census": outcome_census,
        },
        "gate_reachability": _gate_wiring(),
        "source_receipts": [{"path": _relative(path), "sha256": _sha256(path)} for path in sources]
        + [
            {
                "path": "artifacts/facts/F-*.json",
                "population": len(fact_paths),
                "sha256": _population_sha256(fact_paths),
            },
            {
                "path": "artifacts/episodes/**/episode*.json excluding fixtures*",
                "population": len(production_episode_paths),
                "sha256": _population_sha256(production_episode_paths),
            },
        ],
    }


def _percent(numerator: int, denominator: int) -> str:
    return "0.0" if denominator == 0 else f"{100 * numerator / denominator:.1f}"


def render(document: dict[str, Any]) -> str:
    kernel = document["kernel_library"]
    links = document["knowledge_connectivity"]
    semantics = document["semantic_coverage"]
    facts = document["fact_ledger"]
    autonomy = document["autonomous_production"]
    episodes = autonomy["production_episodes"]
    multi = autonomy["reusable_multi_target_operations"]
    outcomes = autonomy["producer_outcome_census"]
    gate_rows = document["gate_reachability"]
    status_counts = facts["status_counts"]
    lines = [
        "# Axeyum product health",
        "",
        "<!-- Generated by scripts/gen-product-health.py; do not edit by hand. -->",
        "",
        (
            "This snapshot measures committed evidence populations and static gate reachability. "
            "It deliberately records runtime gate status as **not recorded**: wired does not mean run, "
            "and a generated dashboard is not CI evidence."
        ),
        "",
        "## Current populations",
        "",
        "| Surface | Measured state | Honest interpretation |",
        "| --- | ---: | --- |",
        f"| Kernel library | {kernel['theorems']:,} theorems; {kernel['axiom_free_declarations']:,}/{kernel['declarations']:,} declarations axiom-free | Checked library scale, not autonomous yield |",
        f"| Fact ledger | {facts['facts']:,} facts; {status_counts.get('proved', 0):,} proved; {status_counts.get('open', 0):,} open | Durable proposition state |",
        f"| Exact lemma links | {links['theorems_with_exact_fact_links']:,}/{links['kernel_theorems']:,} ({_percent(links['theorems_with_exact_fact_links'], links['kernel_theorems'])}%) | Remaining theorems are searchable but not exactly fact-linked |",
        f"| Reviewed semantic coverage | {semantics['qualified_formalization_facts']:,} facts; {semantics['kernel_semantic_anchors']:,} kernel anchors across {semantics['concepts']:,} projected concepts | Qualified partial mappings, not automated classification |",
        f"| Registered producers | {autonomy['authoritative_operations']:,} authoritative; {len(multi):,} reusable multi-target | Registration breadth is not conversion rate |",
        f"| Production episodes | {episodes['production_episodes']:,}; {episodes['fixture_episodes_excluded']:,} fixtures excluded | Nonzero real evidence population |",
        f"| General producer observations | {outcomes['outcomes'].get('admissible-proof', 0):,}/{outcomes['observed_facts']:,} admissible | Current measured autonomous-search weakness |",
        "",
        "## Reusable operation families",
        "",
        "| Operation | Registered facts |",
        "| --- | ---: |",
    ]
    lines.extend(f"| `{row['id']}` | {row['fact_count']} |" for row in multi)
    lines.extend(
        [
            "",
            "## Canonical gate reachability",
            "",
            "| Authority | `just check` | shell fallback |",
            "| --- | --- | --- |",
        ]
    )
    for name, row in gate_rows.items():
        lines.append(
            f"| `{name}` | {'yes' if row['just_check'] else 'NO'} | {'yes' if row['shell_fallback'] else 'NO'} |"
        )
    lines.extend(
        [
            "",
            "## What this says to do next",
            "",
            "1. Raise measured general-producer conversion without per-target operations.",
            "2. Increase exact fact-to-kernel connectivity while keeping unresolved identities explicit.",
            "3. Add authenticated runtime gate/CI receipts before this dashboard can report execution health.",
            "",
            (
                "The source hashes used to derive this page are retained in "
                "[`artifacts/product-health-v1.json`](../../../artifacts/product-health-v1.json)."
            ),
            "",
        ]
    )
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if generated outputs are stale")
    args = parser.parse_args(argv)
    try:
        document = build()
        json_bytes = (json.dumps(document, indent=2, sort_keys=True) + "\n").encode()
        markdown = render(document).encode()
    except (HealthError, OSError, KeyError, TypeError) as error:
        print(f"PRODUCT_HEALTH_ERROR|{error}", file=sys.stderr)
        return 2

    expected = ((JSON_OUT, json_bytes), (MARKDOWN_OUT, markdown))
    if args.check:
        stale = [
            _relative(path)
            for path, content in expected
            if not path.exists() or path.read_bytes() != content
        ]
        if stale:
            print(f"PRODUCT_HEALTH_STALE|paths={','.join(stale)}", file=sys.stderr)
            return 1
    else:
        for path, content in expected:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)

    print(
        "PRODUCT_HEALTH|"
        f"facts={document['fact_ledger']['facts']}|"
        f"theorems={document['kernel_library']['theorems']}|"
        f"linked={document['knowledge_connectivity']['theorems_with_exact_fact_links']}|"
        f"episodes={document['autonomous_production']['production_episodes']['production_episodes']}|"
        f"runtime={document['runtime_gate_status']['state']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
