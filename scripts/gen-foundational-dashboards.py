#!/usr/bin/env python3
"""Generate Markdown dashboards for the foundational concept atlas."""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
ATLAS = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"
EXAMPLE_ROOT = ROOT / "artifacts" / "examples" / "math"
LEARN_ROOT = ROOT / "docs" / "learn" / "math"
OUT_DIR = ROOT / "docs" / "foundational-resources" / "generated"

GATES = {
    0: "R0 source anchor",
    1: "R1 concept row",
    2: "R2 example pack",
    3: "R3 learner path",
    4: "R4 checked evidence",
    5: "R5 solver reuse",
    6: "R6 consumer boundary",
}
EVIDENCE_STATUSES = {"checked", "replay-only", "lean-horizon", "not-required"}
SOLVER_REUSE_MARKERS = (
    "crates/",
    "tests/",
    "corpus/",
    "bench-results/",
    "cargo test",
    "fuzz",
    "benchmark",
    "proof_regression",
    "farkas_regression",
)
FRAGMENT_PRESSURE_BUCKETS = (
    {
        "id": "bool_cnf",
        "label": "Bool / CNF",
        "tokens": ("bool", "cnf", "truth-table", "boolean-cnf-lrat"),
    },
    {
        "id": "qf_bv",
        "label": "QF_BV / Bit-Blast",
        "tokens": ("qf_bv", "qf-bv", " bv", "bv /", "bit-blast", "bitblast"),
    },
    {
        "id": "qf_lia",
        "label": "QF_LIA / Diophantine",
        "tokens": ("qf_lia", "qf-lia", " lia", "lia /", "diophantine", "integer"),
    },
    {
        "id": "qf_lra",
        "label": "QF_LRA / Farkas",
        "tokens": ("qf_lra", "qf-lra", "lra (", "lra /", "farkas", "exact rational"),
    },
    {
        "id": "qf_uf",
        "label": "QF_UF / Alethe",
        "tokens": ("qf_uf", "qf-uf", "euf", "alethe", "congruence"),
    },
    {
        "id": "nra_rcf",
        "label": "NRA / RCF Shadows",
        "tokens": ("nra", "real-closed-field", "rcf", "polynomial constraints"),
    },
    {
        "id": "finite_replay",
        "label": "Finite Replay / Computable Witness",
        "tokens": ("finite-model-replay", "finite model replay", "replay"),
        "proof_status": "replay-only",
    },
    {
        "id": "lean_horizon",
        "label": "Lean Horizon",
        "tokens": ("lean horizon", "lean-horizon", "proof-assistant"),
        "proof_status": "lean-horizon",
    },
)


def load_rows() -> list[dict[str, Any]]:
    with ATLAS.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    return data["rows"]


def load_example_packs() -> list[dict[str, Any]]:
    packs = []
    for metadata_path in sorted(EXAMPLE_ROOT.glob("*/metadata.json")):
        with metadata_path.open("r", encoding="utf-8") as handle:
            metadata = json.load(handle)
        if metadata["claim_status"] == "template":
            continue
        expected_path = metadata_path.parent / "expected.json"
        with expected_path.open("r", encoding="utf-8") as handle:
            expected = json.load(handle)
        packs.append(
            {
                "path": metadata_path.parent.relative_to(ROOT).as_posix(),
                "metadata": metadata,
                "expected": expected,
            }
        )
    return packs


def load_learner_refs() -> dict[str, list[str]]:
    refs: dict[str, list[str]] = defaultdict(list)
    for lesson_path in sorted(LEARN_ROOT.glob("*.md")):
        text = lesson_path.read_text(encoding="utf-8")
        lesson_rel = lesson_path.relative_to(ROOT).as_posix()
        for metadata_path in sorted(EXAMPLE_ROOT.glob("*/metadata.json")):
            pack_id = metadata_path.parent.name
            pack_path = metadata_path.parent.relative_to(ROOT).as_posix()
            if pack_id in text or pack_path in text:
                refs[pack_id].append(lesson_rel)
    return refs


def md_list(values: list[str]) -> str:
    return ", ".join(f"`{value}`" for value in values) if values else "-"


def md_links(paths: list[str]) -> str:
    if not paths:
        return "-"
    links = []
    for path in paths:
        target = Path(path)
        label = target.name
        if path.startswith("docs/learn/math/"):
            target_text = "../../learn/math/" + label
        else:
            target_text = path
        links.append(f"[{label}]({target_text})")
    return ", ".join(links)


def table_cell(value: str) -> str:
    return value.replace("\n", " ").replace("|", "\\|")


def gate_label(level: int) -> str:
    return GATES[level]


def next_gate_label(level: int) -> str:
    if level >= max(GATES):
        return "no later gate"
    return gate_label(level + 1)


def strings_in(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, dict):
        strings: list[str] = []
        for item in value.values():
            strings.extend(strings_in(item))
        return strings
    if isinstance(value, list):
        strings = []
        for item in value:
            strings.extend(strings_in(item))
        return strings
    return []


def pack_pressure_text(pack: dict[str, Any]) -> str:
    metadata = pack["metadata"]
    expected = pack["expected"]
    reuse = metadata.get("solver_reuse") or {}
    values: list[str] = []
    values.extend(strings_in(metadata.get("axeyum_fragments", [])))
    values.extend(strings_in(metadata.get("source_refs", [])))
    values.extend(strings_in(reuse))
    for check in expected.get("checks", []):
        values.append(check.get("validation", ""))
        values.append(check.get("proof_status", ""))
        values.append(check.get("notes", ""))
        values.extend(strings_in(check.get("data", {})))
    return "\n".join(values).lower()


def has_solver_reuse(value: Any) -> bool:
    text = "\n".join(strings_in(value)).lower()
    return any(marker in text for marker in SOLVER_REUSE_MARKERS)


def solver_reuse_status(metadata: dict[str, Any]) -> str:
    reuse = metadata.get("solver_reuse")
    if not reuse:
        return "unclassified"
    return reuse["status"]


def solver_reuse_label(metadata: dict[str, Any]) -> str:
    reuse = metadata.get("solver_reuse")
    if not reuse:
        return "`unclassified`"
    return f"`{reuse['status']}`: {table_cell(reuse['target'])}"


def pack_has_evidence(pack: dict[str, Any]) -> bool:
    return any(
        check.get("proof_status") in EVIDENCE_STATUSES
        for check in pack["expected"].get("checks", [])
    )


def pack_gate(
    pack: dict[str, Any],
    learner_refs: dict[str, list[str]],
    atlas_pack_ids: set[str],
) -> int:
    metadata = pack["metadata"]
    pack_id = metadata["id"]
    gate = 0
    if pack_id in atlas_pack_ids:
        gate = 1
    if pack["path"] and pack["expected"].get("pack_id") == pack_id:
        gate = max(gate, 2)
    if learner_status(learner_refs.get(pack_id, [])) != "missing":
        gate = max(gate, 3)
    if pack_has_evidence(pack):
        gate = max(gate, 4)
    if (
        solver_reuse_status(metadata) == "promoted"
        or has_solver_reuse(metadata.get("source_refs", []))
        or has_solver_reuse(pack["expected"])
    ):
        gate = max(gate, 5)
    if gate >= 5 and pack_id in atlas_pack_ids:
        gate = 6
    return gate


def pack_gate_map(
    packs: list[dict[str, Any]],
    learner_refs: dict[str, list[str]],
    atlas_pack_ids: set[str],
) -> dict[str, int]:
    return {
        pack["metadata"]["id"]: pack_gate(pack, learner_refs, atlas_pack_ids)
        for pack in packs
    }


def atlas_validated_pack_ids(rows: list[dict[str, Any]]) -> set[str]:
    return {
        pack["id"]
        for row in rows
        for pack in row["example_packs"]
        if pack["status"] == "validated"
    }


def row_gate(row: dict[str, Any], pack_gates: dict[str, int]) -> int:
    gate = 1
    row_packs = row["example_packs"]
    if any(pack["status"] == "validated" for pack in row_packs):
        gate = max(gate, 2)
    if any(pack_gates.get(pack["id"], 0) >= 3 for pack in row_packs):
        gate = max(gate, 3)
    if any(route["status"] in EVIDENCE_STATUSES for route in row["proof_routes"]) or any(
        pack_gates.get(pack["id"], 0) >= 4 for pack in row_packs
    ):
        gate = max(gate, 4)
    if has_solver_reuse(row["proof_routes"]) or has_solver_reuse(row["source_refs"]):
        gate = max(gate, 5)
    if gate >= 5:
        gate = 6
    return gate


def recipe_links(metadata: dict[str, Any]) -> list[str]:
    return [
        source
        for source in metadata["source_refs"]
        if source.startswith("docs/proof-cookbook/recipes/")
    ]


def recipe_list(metadata: dict[str, Any]) -> str:
    recipes = [Path(source).name for source in recipe_links(metadata)]
    return md_list(recipes)


def upgrade_recipes(metadata: dict[str, Any]) -> list[str]:
    return sorted(
        Path(source).name
        for source in recipe_links(metadata)
        if Path(source).name != "finite-model-replay.md"
    )


def upgrade_recipe_list(metadata: dict[str, Any]) -> str:
    recipes = upgrade_recipes(metadata)
    return md_list(recipes) if recipes else "`needs-proof-route`"


def learner_status(lesson_refs: list[str]) -> str:
    focused = [
        ref
        for ref in lesson_refs
        if ref.startswith("docs/learn/math/")
        and ref.endswith("-end-to-end.md")
        and Path(ref).name != "README.md"
    ]
    path_only = [
        ref
        for ref in lesson_refs
        if ref.startswith("docs/learn/math/")
        and not ref.endswith("-end-to-end.md")
        and Path(ref).name != "README.md"
    ]
    index = [ref for ref in lesson_refs if Path(ref).name == "README.md"]
    if focused:
        return "focused"
    if path_only:
        return "path-only"
    if index:
        return "index-only"
    return "missing"


def proof_counts(checks: list[dict[str, Any]], *, include_checked: bool) -> Counter[str]:
    counts: Counter[str] = Counter()
    for check in checks:
        status = check["proof_status"]
        if include_checked or status not in {"checked", "not-required"}:
            counts[status] += 1
    return counts


def count_text(counts: Counter[str]) -> str:
    return ", ".join(f"`{key}`: {counts[key]}" for key in sorted(counts)) or "-"


def expected_result_counts(checks: list[dict[str, Any]]) -> Counter[str]:
    return Counter(check["expected_result"] for check in checks)


def unsat_check_ids(checks: list[dict[str, Any]]) -> list[str]:
    return [check["id"] for check in checks if check["expected_result"] == "unsat"]


def pressure_buckets_for_pack(pack: dict[str, Any]) -> list[dict[str, Any]]:
    text = pack_pressure_text(pack)
    proof_statuses = {check["proof_status"] for check in pack["expected"].get("checks", [])}
    buckets = []
    for bucket in FRAGMENT_PRESSURE_BUCKETS:
        proof_status = bucket.get("proof_status")
        if proof_status and proof_status in proof_statuses:
            buckets.append(bucket)
            continue
        if any(token in text for token in bucket["tokens"]):
            buckets.append(bucket)
    return buckets


def pack_list(row: dict[str, Any]) -> str:
    return ", ".join(f"`{pack['id']}` ({pack['status']})" for pack in row["example_packs"])


def write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def math_coverage(rows: list[dict[str, Any]], pack_gates: dict[str, int]) -> str:
    curriculum_rows = [row for row in rows if row["kind"] == "curriculum-node"]
    lines = [
        "# Math Curriculum Coverage",
        "",
        "Generated by `python3 scripts/gen-foundational-dashboards.py`.",
        "",
        "| Curriculum Node | Status | Gate | Next Gate | Decidability | Fields | First Pack | Proof Route |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for row in curriculum_rows:
        proof = "; ".join(f"{route['status']}: {route['name']}" for route in row["proof_routes"])
        gate = row_gate(row, pack_gates)
        lines.append(
            "| "
            f"`{row['curriculum_node']}` | "
            f"`{row['curriculum_status']}` / `{row['resource_status']}` | "
            f"`{gate_label(gate)}` | "
            f"`{next_gate_label(gate)}` | "
            f"`{row['decidability']}` | "
            f"{md_list(row['field_ids'])} | "
            f"{pack_list(row)} | "
            f"{proof} |"
        )
    lines.extend(
        [
            "",
            "## Totals",
            "",
        ]
    )
    for key, count in sorted(Counter(row["curriculum_status"] for row in curriculum_rows).items()):
        lines.append(f"- `{key}`: {count}")
    lines.append("")
    return "\n".join(lines)


def curriculum_status_audit_reason(
    row: dict[str, Any],
    validated_pack_ids: list[str],
    checks: list[dict[str, Any]],
) -> tuple[str, str, str, str]:
    source_status = row["curriculum_status"]
    resource_status = row["resource_status"]
    has_validated_pack = bool(validated_pack_ids)
    has_checked = any(check.get("proof_status") == "checked" for check in checks)
    has_lean_horizon = source_status == "lean-horizon" or any(
        check.get("proof_status") == "lean-horizon" for check in checks
    ) or any(route["status"] == "lean-horizon" for route in row["proof_routes"])

    if not has_validated_pack:
        return (
            "missing-pack",
            "planned",
            "No validated example pack is linked to this curriculum row.",
            "Build the first R2 example pack or keep the row explicitly planned.",
        )
    if source_status == "planned":
        recommendation = (
            "review-covered-or-lean-horizon" if has_lean_horizon else "review-covered"
        )
        reason = (
            "Validated resource packs exist, but the curriculum DAG still says `planned`."
        )
        if has_checked:
            reason += " At least one linked row has checked evidence."
        return (
            "source-planned-resource-validated",
            recommendation,
            reason,
            "Audit the source status: use `covered` for a mature finite/computable "
            "slice or `lean-horizon` when the general theorem is the real target.",
        )
    if source_status == "covered":
        if resource_status == "validated":
            return (
                "aligned-covered",
                "covered",
                "The curriculum DAG says `covered` and linked resource packs validate.",
                "No source-status change required; continue proof and solver-reuse upgrades.",
            )
        return (
            "covered-with-resource-gap",
            "review",
            "The curriculum DAG says `covered`, but the generated resource status is not `validated`.",
            "Either link a validating pack or document why the source row remains covered.",
        )
    if source_status == "lean-horizon":
        return (
            "bounded-evidence-lean-horizon",
            "lean-horizon",
            "Validated bounded or finite resource packs exist, but the general "
            "theorem layer remains a Lean horizon.",
            "Keep the bounded-vs-general boundary explicit until no-sorry Lean evidence lands.",
        )
    return (
        "review",
        "review",
        "The source status does not match a known audit category.",
        "Inspect the curriculum row and generated resource evidence manually.",
    )


def curriculum_status_audit_dashboard(
    rows: list[dict[str, Any]],
    packs: list[dict[str, Any]],
    pack_gates: dict[str, int],
) -> str:
    packs_by_id = {pack["metadata"]["id"]: pack for pack in packs}
    curriculum_rows = [row for row in rows if row["kind"] == "curriculum-node"]
    audit_rows = []
    audit_counts: Counter[str] = Counter()
    source_counts: Counter[str] = Counter()
    recommendation_counts: Counter[str] = Counter()

    for row in curriculum_rows:
        validated_pack_ids = [
            pack["id"] for pack in row["example_packs"] if pack["status"] == "validated"
        ]
        linked_packs = [
            packs_by_id[pack_id]
            for pack_id in validated_pack_ids
            if pack_id in packs_by_id
        ]
        checks = [
            check
            for pack in linked_packs
            for check in pack["expected"].get("checks", [])
        ]
        audit, recommendation, reason, next_action = curriculum_status_audit_reason(
            row,
            validated_pack_ids,
            checks,
        )
        audit_counts[audit] += 1
        source_counts[row["curriculum_status"]] += 1
        recommendation_counts[recommendation] += 1
        audit_rows.append(
            (
                audit,
                row["curriculum_node"],
                row["curriculum_status"],
                row["resource_status"],
                recommendation,
                gate_label(row_gate(row, pack_gates)),
                next_gate_label(row_gate(row, pack_gates)),
                validated_pack_ids,
                count_text(proof_counts(checks, include_checked=True)),
                reason,
                next_action,
            )
        )

    audit_rows.sort()
    lines = [
        "# Curriculum Status Audit",
        "",
        "Generated by `python3 scripts/gen-foundational-dashboards.py`.",
        "",
        "This dashboard separates the source curriculum status in",
        "`docs/curriculum/curriculum.toml` from the generated resource maturity",
        "visible through validated packs, proof rows, learner links, and solver",
        "reuse gates. It is intentionally conservative: it does not rewrite the",
        "curriculum DAG, but it identifies rows whose source status now deserves",
        "an explicit `covered` versus `lean-horizon` decision.",
        "",
        "## Summary",
        "",
        f"- curriculum rows: {len(curriculum_rows)}",
        "",
        "### Source Status Totals",
        "",
    ]
    for status, count in sorted(source_counts.items()):
        lines.append(f"- `{status}`: {count}")
    lines.extend(["", "### Audit Totals", ""])
    for audit, count in sorted(audit_counts.items()):
        lines.append(f"- `{audit}`: {count}")
    lines.extend(["", "### Recommendation Totals", ""])
    for recommendation, count in sorted(recommendation_counts.items()):
        lines.append(f"- `{recommendation}`: {count}")

    lines.extend(
        [
            "",
            "## Detail",
            "",
            "| Audit | Curriculum Node | Source Status | Resource Status | "
            "Recommendation | Gate | Next Gate | Validated Packs | "
            "Proof Status Counts | Reason | Next Action |",
            "|---|---|---|---|---|---|---|---|---|---|---|",
        ]
    )
    for (
        audit,
        node_id,
        source_status,
        resource_status,
        recommendation,
        gate,
        next_gate,
        validated_pack_ids,
        proof_status_counts,
        reason,
        next_action,
    ) in audit_rows:
        lines.append(
            "| "
            f"`{audit}` | "
            f"`{node_id}` | "
            f"`{source_status}` | "
            f"`{resource_status}` | "
            f"`{recommendation}` | "
            f"`{gate}` | "
            f"`{next_gate}` | "
            f"{md_list(validated_pack_ids)} | "
            f"{proof_status_counts} | "
            f"{table_cell(reason)} | "
            f"{table_cell(next_action)} |"
        )
    lines.append("")
    return "\n".join(lines)


def field_dashboard(rows: list[dict[str, Any]], pack_gates: dict[str, int]) -> str:
    by_field: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        for field_id in row["field_ids"]:
            by_field[field_id].append(row)
    lines = [
        "# Math Field Dashboard",
        "",
        "Generated by `python3 scripts/gen-foundational-dashboards.py`.",
        "",
        "| Field | Rows | Gate Levels | Next Gates | Curriculum Nodes | Decidability Classes | Example Packs |",
        "|---|---:|---|---|---|---|---|",
    ]
    for field_id in sorted(by_field):
        field_rows = by_field[field_id]
        curriculum_nodes = [
            row["curriculum_node"] for row in field_rows if row["kind"] == "curriculum-node"
        ]
        decidability = sorted({row["decidability"] for row in field_rows})
        packs = sorted({pack["id"] for row in field_rows for pack in row["example_packs"]})
        gates = sorted({row_gate(row, pack_gates) for row in field_rows})
        next_gates = sorted({next_gate_label(gate) for gate in gates})
        lines.append(
            "| "
            f"`{field_id}` | "
            f"{len(field_rows)} | "
            f"{md_list([gate_label(gate) for gate in gates])} | "
            f"{md_list(next_gates)} | "
            f"{md_list(curriculum_nodes)} | "
            f"{md_list(decidability)} | "
            f"{md_list(packs)} |"
        )
    lines.append("")
    return "\n".join(lines)


def pack_route_coverage(packs: list[dict[str, Any]], pack_gates: dict[str, int]) -> list[str]:
    lines = [
        "## Example Pack Route Coverage",
        "",
        "| Pack | Gate | Next Gate | Solver Reuse | Trust Status | Check Status Counts | Recipe Links | Validator |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for pack in packs:
        metadata = pack["metadata"]
        counts = proof_counts(pack["expected"]["checks"], include_checked=True)
        gate = pack_gates[metadata["id"]]
        lines.append(
            "| "
            f"`{metadata['id']}` | "
            f"`{gate_label(gate)}` | "
            f"`{next_gate_label(gate)}` | "
            f"{solver_reuse_label(metadata)} | "
            f"`{metadata['trust_status']}` | "
            f"{count_text(counts)} | "
            f"{recipe_list(metadata)} | "
            f"`{metadata['validator_command']}` |"
        )
    lines.append("")
    return lines


def pack_solver_reuse_queue(packs: list[dict[str, Any]], pack_gates: dict[str, int]) -> list[str]:
    rows: list[tuple[str, str, str, str, str, str, str, str]] = []
    for pack in packs:
        metadata = pack["metadata"]
        reuse = metadata.get("solver_reuse")
        if not reuse:
            continue
        rows.append(
            (
                reuse["status"],
                metadata["id"],
                gate_label(pack_gates[metadata["id"]]),
                next_gate_label(pack_gates[metadata["id"]]),
                reuse["target"],
                reuse["pressure"],
                ",".join(reuse["evidence"]),
                reuse["next_step"],
            )
        )
    rows.sort()
    lines = [
        "## Example Pack Solver Reuse Queue",
        "",
        "| Status | Pack | Gate | Next Gate | Target | Pressure | Evidence Rows | Next Step |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for status, pack_id, gate, next_gate, target, pressure, evidence, next_step in rows:
        lines.append(
            "| "
            f"`{status}` | "
            f"`{pack_id}` | "
            f"`{gate}` | "
            f"`{next_gate}` | "
            f"{table_cell(target)} | "
            f"{table_cell(pressure)} | "
            f"`{table_cell(evidence)}` | "
            f"{table_cell(next_step)} |"
        )
    lines.extend(["", "### Solver Reuse Status Totals", ""])
    for status, count in sorted(Counter(status for status, *_ in rows).items()):
        lines.append(f"- `{status}`: {count}")
    if not rows:
        lines.append("- none")
    lines.append("")
    return lines


def pack_evidence_gaps(
    packs: list[dict[str, Any]], pack_gates: dict[str, int]
) -> list[str]:
    rows: list[tuple[str, str, str, str, str, str, str, str, str, str]] = []
    for pack in packs:
        metadata = pack["metadata"]
        recipes = recipe_list(metadata)
        fragments = ",".join(metadata["axeyum_fragments"])
        fields = ",".join(metadata["field_ids"])
        gate = pack_gates[metadata["id"]]
        for check in pack["expected"]["checks"]:
            proof_status = check["proof_status"]
            if proof_status in {"checked", "not-required"}:
                continue
            rows.append(
                (
                    proof_status,
                    metadata["id"],
                    gate_label(gate),
                    next_gate_label(gate),
                    check["id"],
                    check["expected_result"],
                    fields,
                    fragments,
                    recipes,
                    check["notes"],
                )
            )
    rows.sort()
    lines = [
        "## Example Pack Evidence Gaps",
        "",
        "| Proof Status | Pack | Gate | Next Gate | Check | Result | Fields | Fragments | Recipe Links | Notes |",
        "|---|---|---|---|---|---|---|---|---|---|",
    ]
    for (
        proof_status,
        pack_id,
        gate,
        next_gate,
        check_id,
        result,
        fields,
        fragments,
        recipes,
        notes,
    ) in rows:
        lines.append(
            "| "
            f"`{proof_status}` | "
            f"`{pack_id}` | "
            f"`{gate}` | "
            f"`{next_gate}` | "
            f"`{check_id}` | "
            f"`{result}` | "
            f"`{table_cell(fields)}` | "
            f"`{table_cell(fragments)}` | "
            f"{recipes} | "
            f"{table_cell(notes)} |"
        )
    lines.extend(
        [
            "",
            "### Pack Evidence Status Totals",
            "",
        ]
    )
    for status, count in sorted(Counter(status for status, *_ in rows).items()):
        lines.append(f"- `{status}`: {count}")
    lines.append("")
    return lines


def proof_gap_dashboard(
    rows: list[dict[str, Any]], packs: list[dict[str, Any]], pack_gates: dict[str, int]
) -> str:
    proof_rows: list[tuple[str, str, str, str, str, str, str]] = []
    for row in rows:
        gate = row_gate(row, pack_gates)
        for route in row["proof_routes"]:
            if route["status"] == "checked":
                continue
            proof_rows.append(
                (
                    route["status"],
                    row["id"],
                    gate_label(gate),
                    next_gate_label(gate),
                    row["decidability"],
                    ",".join(row["field_ids"]),
                    route["name"],
                )
            )
    proof_rows.sort()
    lines = [
        "# Proof Gap Dashboard",
        "",
        "Generated by `python3 scripts/gen-foundational-dashboards.py`.",
        "",
        "## Concept Atlas Gaps",
        "",
        "| Proof Status | Row | Gate | Next Gate | Decidability | Fields | Route |",
        "|---|---|---|---|---|---|---|",
    ]
    for status, row_id, gate, next_gate, decidability, fields, route in proof_rows:
        lines.append(
            "| "
            f"`{status}` | "
            f"`{row_id}` | "
            f"`{gate}` | "
            f"`{next_gate}` | "
            f"`{decidability}` | "
            f"`{fields}` | "
            f"{route} |"
        )
    lines.extend(
        [
            "",
            "## Status Totals",
            "",
        ]
    )
    for status, count in sorted(Counter(status for status, *_ in proof_rows).items()):
        lines.append(f"- `{status}`: {count}")
    lines.append("")
    lines.extend(pack_route_coverage(packs, pack_gates))
    lines.extend(pack_solver_reuse_queue(packs, pack_gates))
    lines.extend(pack_evidence_gaps(packs, pack_gates))
    return "\n".join(lines)


def learner_proof_upgrade_dashboard(
    packs: list[dict[str, Any]],
    learner_refs: dict[str, list[str]],
    pack_gates: dict[str, int],
) -> str:
    learner_rows = []
    proof_rows = []
    learner_totals: Counter[str] = Counter()
    route_totals: Counter[str] = Counter()
    nonchecked_check_total = 0

    for pack in packs:
        metadata = pack["metadata"]
        expected = pack["expected"]
        refs = sorted(learner_refs.get(metadata["id"], []))
        status = learner_status(refs)
        gate = pack_gates[metadata["id"]]
        learner_totals[status] += 1
        all_counts = proof_counts(expected["checks"], include_checked=True)
        learner_rows.append(
            (
                status,
                metadata["id"],
                gate_label(gate),
                next_gate_label(gate),
                solver_reuse_label(metadata),
                ",".join(metadata["field_ids"]),
                metadata["trust_status"],
                count_text(all_counts),
                refs,
            )
        )

        nonchecked_counts = proof_counts(expected["checks"], include_checked=False)
        if nonchecked_counts:
            nonchecked_check_total += sum(nonchecked_counts.values())
            route_names = upgrade_recipes(metadata) or ["needs-proof-route"]
            routes = md_list(route_names)
            for route in route_names:
                route_totals[route] += 1
            proof_rows.append(
                (
                    routes,
                    metadata["id"],
                    gate_label(gate),
                    next_gate_label(gate),
                    solver_reuse_label(metadata),
                    status,
                    metadata["trust_status"],
                    count_text(nonchecked_counts),
                    ",".join(metadata["axeyum_fragments"]),
                    refs,
                )
            )

    learner_rows.sort()
    proof_rows.sort()

    lines = [
        "# Learner And Proof Upgrade Dashboard",
        "",
        "Generated by `python3 scripts/gen-foundational-dashboards.py`.",
        "",
        "This dashboard is intentionally mechanical: a pack counts as learner-linked",
        "only when a `docs/learn/math` page explicitly mentions the pack id or path.",
        "",
        "## Summary",
        "",
        f"- math example packs: {len(packs)}",
        f"- packs with non-checked proof rows: {len(proof_rows)}",
        f"- non-checked proof rows: {nonchecked_check_total}",
        "",
        "### Learner Status Totals",
        "",
    ]
    for status, count in sorted(learner_totals.items()):
        lines.append(f"- `{status}`: {count}")
    lines.extend(["", "### Candidate Proof Route Totals", ""])
    for route, count in sorted(route_totals.items()):
        lines.append(f"- `{route}`: {count}")
    lines.extend(
        [
            "",
            "## Learner Coverage",
            "",
            "| Learner Status | Pack | Gate | Next Gate | Solver Reuse | Fields | Trust Status | Proof Status Counts | Learner Pages |",
            "|---|---|---|---|---|---|---|---|---|",
        ]
    )
    for (
        status,
        pack_id,
        gate,
        next_gate,
        solver_reuse,
        fields,
        trust_status,
        counts,
        refs,
    ) in learner_rows:
        lines.append(
            "| "
            f"`{status}` | "
            f"`{pack_id}` | "
            f"`{gate}` | "
            f"`{next_gate}` | "
            f"{solver_reuse} | "
            f"`{table_cell(fields)}` | "
            f"`{trust_status}` | "
            f"{counts} | "
            f"{md_links(refs)} |"
        )
    lines.extend(
        [
            "",
            "## Focused Lesson Queue",
            "",
            "| Learner Status | Pack | Current Learner Pages |",
            "|---|---|---|",
        ]
    )
    for (
        status,
        pack_id,
        _gate,
        _next_gate,
        _solver_reuse,
        _fields,
        _trust_status,
        _counts,
        refs,
    ) in learner_rows:
        if status == "focused":
            continue
        lines.append(
            "| "
            f"`{status}` | "
            f"`{pack_id}` | "
            f"{md_links(refs)} |"
        )
    lines.extend(
        [
            "",
            "## Proof Upgrade Queue",
            "",
            "| Candidate Route | Pack | Gate | Next Gate | Solver Reuse | Learner Status | Trust Status | Non-Checked Rows | Fragments | Learner Pages |",
            "|---|---|---|---|---|---|---|---|---|---|",
        ]
    )
    for (
        routes,
        pack_id,
        gate,
        next_gate,
        solver_reuse,
        status,
        trust_status,
        counts,
        fragments,
        refs,
    ) in proof_rows:
        lines.append(
            "| "
            f"{routes} | "
            f"`{pack_id}` | "
            f"`{gate}` | "
            f"`{next_gate}` | "
            f"{solver_reuse} | "
            f"`{status}` | "
            f"`{trust_status}` | "
            f"{counts} | "
            f"`{table_cell(fragments)}` | "
            f"{md_links(refs)} |"
        )
    lines.append("")
    return "\n".join(lines)


def curriculum_pressure_by_fragment_dashboard(
    packs: list[dict[str, Any]],
    pack_gates: dict[str, int],
) -> str:
    bucket_rows: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for pack in packs:
        for bucket in pressure_buckets_for_pack(pack):
            bucket_rows[bucket["id"]].append(pack)

    lines = [
        "# Curriculum Pressure By Fragment",
        "",
        "Generated by `python3 scripts/gen-foundational-dashboards.py`.",
        "",
        "This view groups math resource packs by the solver/proof pressure they",
        "create for Axeyum. Buckets are intentionally overlapping: a finite",
        "probability pack can pressure both finite replay and QF_LRA/Farkas, and",
        "a topology pack can pressure both finite replay and Lean-horizon rows.",
        "",
        "The grouping is derived from pack metadata, proof-cookbook links,",
        "`solver_reuse` records, validation names, and expected-result proof",
        "statuses. It is a planning surface, not a solver parity claim.",
        "",
        "## Summary",
        "",
        "| Pressure Bucket | Packs | Checks | Results | Proof Statuses | Promoted Solver Reuse | Fields |",
        "|---|---:|---:|---|---|---:|---|",
    ]
    for bucket in FRAGMENT_PRESSURE_BUCKETS:
        bucket_id = bucket["id"]
        bucket_packs = sorted(bucket_rows.get(bucket_id, []), key=lambda pack: pack["metadata"]["id"])
        checks = [check for pack in bucket_packs for check in pack["expected"]["checks"]]
        fields = sorted({field for pack in bucket_packs for field in pack["metadata"]["field_ids"]})
        promoted = sum(
            1
            for pack in bucket_packs
            if solver_reuse_status(pack["metadata"]) == "promoted"
        )
        lines.append(
            "| "
            f"{bucket['label']} | "
            f"{len(bucket_packs)} | "
            f"{len(checks)} | "
            f"{count_text(expected_result_counts(checks))} | "
            f"{count_text(proof_counts(checks, include_checked=True))} | "
            f"{promoted} | "
            f"{md_list(fields)} |"
        )

    lines.extend(
        [
            "",
            "## Pack Detail",
            "",
            "| Pressure Bucket | Pack | Gate | Next Gate | Solver Reuse | Fields | Fragments | Proof Statuses | Unsat Checks |",
            "|---|---|---|---|---|---|---|---|---|",
        ]
    )
    for bucket in FRAGMENT_PRESSURE_BUCKETS:
        bucket_id = bucket["id"]
        for pack in sorted(bucket_rows.get(bucket_id, []), key=lambda item: item["metadata"]["id"]):
            metadata = pack["metadata"]
            checks = pack["expected"]["checks"]
            gate = pack_gates[metadata["id"]]
            lines.append(
                "| "
                f"{bucket['label']} | "
                f"`{metadata['id']}` | "
                f"`{gate_label(gate)}` | "
                f"`{next_gate_label(gate)}` | "
                f"{solver_reuse_label(metadata)} | "
                f"{md_list(metadata['field_ids'])} | "
                f"{md_list(metadata['axeyum_fragments'])} | "
                f"{count_text(proof_counts(checks, include_checked=True))} | "
                f"{md_list(unsat_check_ids(checks))} |"
            )

    lines.extend(
        [
            "",
            "## How To Use This",
            "",
            "- Use `Bool / CNF`, `QF_BV`, `QF_LIA`, `QF_LRA`, and `QF_UF` buckets to pick solver-regression or proof-route candidates.",
            "- Use `Finite Replay / Computable Witness` to find packs that teach source-level model checking but may not need solver promotion.",
            "- Use `Lean Horizon` to find bounded examples whose general theorem is explicitly outside current SMT coverage.",
            "- Treat a pack in multiple buckets as a signal that the learner story and solver/proof story should stay separated in docs.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    rows = load_rows()
    packs = load_example_packs()
    learner_refs = load_learner_refs()
    atlas_pack_ids = atlas_validated_pack_ids(rows)
    pack_gates = pack_gate_map(packs, learner_refs, atlas_pack_ids)
    write(OUT_DIR / "math-coverage.md", math_coverage(rows, pack_gates))
    write(
        OUT_DIR / "curriculum-status-audit.md",
        curriculum_status_audit_dashboard(rows, packs, pack_gates),
    )
    write(OUT_DIR / "math-field-dashboard.md", field_dashboard(rows, pack_gates))
    write(OUT_DIR / "proof-gap-dashboard.md", proof_gap_dashboard(rows, packs, pack_gates))
    write(
        OUT_DIR / "learner-proof-upgrade-dashboard.md",
        learner_proof_upgrade_dashboard(packs, learner_refs, pack_gates),
    )
    write(
        OUT_DIR / "curriculum-pressure-by-fragment.md",
        curriculum_pressure_by_fragment_dashboard(packs, pack_gates),
    )
    print("generated foundational resource dashboards")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
