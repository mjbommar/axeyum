#!/usr/bin/env python3
"""Validate the TL2.13 M0 mutual-inductive source/wire freeze fail closed."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "docs" / "plan" / "lean-mutual-inductive-groups-v1.json"
SCRIPTS = str(ROOT / "scripts")
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

from prototype_lean4export_census import census_bytes  # noqa: E402


SCHEMA = "axeyum-lean-mutual-inductive-groups-v1"
TOP_LEVEL_KEYS = {
    "schema",
    "stage",
    "date",
    "decision",
    "plan",
    "baseline",
    "pins",
    "resource_policy",
    "commands",
    "semantic_contract",
    "source",
    "streams",
    "case_ids",
    "mutation_ids",
    "generated_grammar",
    "mandatory_controls",
    "stop_condition_ids",
    "claim_limits",
    "next",
}
EXPECTED_PINS = {
    "lean": {
        "toolchain": "leanprover/lean4:v4.30.0",
        "version": "4.30.0",
        "git_commit": "d024af099ca4bf2c86f649261ebf59565dc8c622",
    },
    "lean4export": {
        "version": "v4.30.0",
        "git_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
        "format": "3.1.0",
    },
}
EXPECTED_RESOURCES = {
    "runner": "systemd-run --user --scope",
    "memory_high": "3G",
    "memory_max": "4G",
    "memory_swap_max": "512M",
    "lean_jobs": 1,
    "rust_jobs": 1,
    "per_stream_max_bytes": 1_048_576,
    "aggregate_stream_max_bytes": 2_097_152,
}
EXPECTED_RUNNER = [
    "systemd-run",
    "--user",
    "--scope",
    "--quiet",
    "-p",
    "MemoryHigh=3G",
    "-p",
    "MemoryMax=4G",
    "-p",
    "MemorySwapMax=512M",
]
EXPECTED_COMPILE = [
    "/usr/bin/time",
    "-v",
    "<pinned-lean>",
    "-j1",
    "-o",
    "AxeyumMutualInductiveComputation.olean",
    "lean-v4.30-mutual-inductive-computation.lean",
]
EXPECTED_EXPORT = [
    "/usr/bin/time",
    "-v",
    "env",
    "PATH=<pinned-lean-bin>:$PATH",
    "LEAN_PATH=<run-directory>",
    "<pinned-lean4export>",
    "AxeyumMutualInductiveComputation",
    "--",
    "<selected-root>",
]
EXPECTED_SEMANTICS = {
    "group": "ordered nonempty [I_0, ..., I_(g-1)]",
    "shared_parameters": (
        "definitionally equal parameter telescope instantiated by one shared local vector"
    ),
    "result_universes": "equivalent across every family",
    "positivity": (
        "one occurrence set containing every group family before provisional insertion"
    ),
    "recursive_field": "u : Pi xs, I_j params recursive_indices",
    "induction_hypothesis": "Pi xs, motive_j recursive_indices (u xs)",
    "rule_argument": (
        "fun xs => I_j.rec params all_motives all_minors recursive_indices (u xs)"
    ),
    "minor_conclusion": "motive_i result_indices (owner_ctor params fields)",
    "motive_order": "family order",
    "minor_order": "family order then constructor order",
    "ih_order": "after all fields, in recursive-field order",
    "recursor_suffix": "owner-family indices then owner-family major",
    "mutual_prop": "elimination restricted to Prop and K-like reduction disabled",
    "publication": "all families, constructors, and recursors or none",
    "singleton": "add_inductive delegates without identity or behavior drift",
    "wire_recursor_order": (
        "descriptive dependency order; match recursors by checked name and owned rules"
    ),
}
EXPECTED_BASELINE = {
    "preregistration_revision": "0527a61a6de3703b94a8bbd59f5295af4a846b4e",
    "semantic_revision": "78f4c5631dbca3fce568be72bde2d906d6e3705f",
    "construct_matrix": {
        "path": "docs/plan/lean-official-construct-matrix-v1.json",
        "sha256": "f6c11499ab38130de75c7acbd7ad1db79afcd080ab405a7233087f8f67c3ac3e",
    },
    "mutual_stream": {
        "path": (
            "docs/plan/fixtures/lean4export-v4.30-construct-matrix-mutual.ndjson"
        ),
        "sha256": "06aa05ccc8abc9309fad04b373017e770da25c7b0c2743fc0f097efd72de3174",
        "bytes": 23_596,
        "records": 395,
        "registered_outcome": (
            "ImportError::Unsupported(line=233,code=inductive-mutual)"
        ),
    },
    "singleton_control": {
        "path": "docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson",
        "sha256": "91df1e44219483b213000b94b06016f9569dc648d0680d9ae91ff3198817db08",
        "registered_outcome": "completed-import",
    },
    "declaration_identity_version": "axeyum-lean-declaration-identity-v1",
}
EXPECTED_SOURCE = {
    "path": "docs/plan/fixtures/lean-v4.30-mutual-inductive-computation.lean",
    "sha256": "d04059e05cbb15d74c6dc526c63e2ac028dfb4b0fe604c9dd3eebdc963e06404",
    "bytes": 1_676,
    "lines": 66,
    "module": "AxeyumMutualInductiveComputation",
    "compile_runs": 2,
    "compile_exit_statuses": [0, 0],
    "compile_elapsed_ms": [460, 220],
    "compile_max_rss_kib": [474_312, 474_740],
    "olean_sha256": "b2582c150c5901728a871919e1c04922f44c11ddeba1a8a446189b6c4d604aba",
}
EXPECTED_ROOTS = [
    {
        "id": "cross-family-computation",
        "selected_root": "AxeyumMutualInductiveComputation.crossFamilyComputes",
        "consumer": "AxeyumMutualInductiveComputation.evenHeight",
        "transition": "EvenTree.rec -> OddTree.rec -> EvenTree.rec",
        "expected_normal_form": "MiniNat.succ (MiniNat.succ MiniNat.zero)",
    },
    {
        "id": "indexed-cross-family-computation",
        "selected_root": (
            "AxeyumMutualInductiveComputation.indexedCrossFamilyComputes"
        ),
        "consumer": "AxeyumMutualInductiveComputation.oddVecHeight",
        "transition": "OddVec.rec -> EvenVec.rec -> OddVec.rec",
        "expected_normal_form": "MiniNat.succ (MiniNat.succ MiniNat.zero)",
    },
]
EXPECTED_CASE_IDS = (
    "singleton-wrapper-control",
    "two-family-cross",
    "mixed-self-cross",
    "three-family-cycle",
    "shared-dependent-params",
    "different-index-counts",
    "indexed-cross",
    "higher-order-cross",
    "multiple-targets",
    "empty-constructor-family",
    "mutual-prop-restriction",
    "empty-group",
    "parameter-mismatch",
    "result-universe-mismatch",
    "cross-negative-domain",
    "cross-invalid-application",
    "duplicate-group-name",
    "late-recursor-failure",
)
EXPECTED_MUTATION_IDS = (
    "motive-omit-duplicate-reorder",
    "owner-motive-for-target",
    "owner-recursor-for-target",
    "minor-omit-duplicate-reorder",
    "family-local-minor-index",
    "all-family-list-drift",
    "parameter-or-uparam-drift",
    "result-universe-or-index-count",
    "cross-occurrence-positivity-miss",
    "ih-field-order",
    "target-index-telescope-field-order",
    "constructor-owner-cidx-nfields-rule",
    "recursor-type-count-rule-nfields",
    "metadata-nonauthority",
    "mutual-prop-or-k-permission",
    "late-failure-no-publication",
)
EXPECTED_STOP_IDS = (
    "lean-group-rule-disagreement",
    "singleton-identity-or-behavior-drift",
    "group-positivity-incomplete-or-singleton-drift",
    "requires-separate-family-publication",
    "target-family-reconstruction-disagreement",
    "self-checks-but-official-differs",
    "official-import-without-complete-comparison",
    "constructor-witness-promoted-to-computation",
    "failure-publishes-group-or-import",
    "mutual-prop-or-k-unsoundness",
    "identity-v1-drift",
    "frontend-lowering-enters-kernel-slice",
    "generated-summary-invalid",
    "resource-cap-exceeded-or-killed",
    "unrelated-dirty-overlap",
)
EXPECTED_GRAMMAR = {
    "seed_policy": "fixed and committed at M3 before the first generated run",
    "minimum_unique_cases": 640,
    "group_sizes": "1..3",
    "shared_parameters": "0..2 including dependent pairs",
    "indices_per_family": "0..2",
    "constructors_per_family": "0..3",
    "recursive_fields": "0..3 among 0..5 total fields",
    "recursive_targets": ["self", "earlier-family", "later-family"],
    "telescope_depth": "0..2",
    "binder_info": ["explicit", "implicit", "strict-implicit"],
    "result_sorts": ["Type", "Prop-restricted"],
    "required_repetitions": 2,
    "summary_identity": "byte-identical",
}
EXPECTED_CONTROLS = {
    "recursive_manifest": "docs/plan/lean-recursive-induction-hypotheses-v1.json",
    "recursive_generated_cases": 768,
    "strict_positivity_manifest": "docs/plan/lean-strict-positivity-v1.json",
    "strict_positivity_generated_cases": 840,
    "official_construct_matrix": "docs/plan/lean-official-construct-matrix-v1.json",
    "transactional_import": "CompletedImport only after full-stream success",
    "declaration_identity_version": "axeyum-lean-declaration-identity-v1",
}
EXPECTED_CLAIMS = {
    "official_source": "accepted-twice",
    "olean_reproducibility": "byte-identical-twice",
    "official_export": "byte-identical-twice-per-root",
    "official_wire_inventory": "frozen",
    "axeyum_import": "not-run-on-new-streams",
    "axeyum_admission": "not-run-on-new-streams",
    "axeyum_computation": "not-run-on-new-streams",
    "mutual_kernel_support": "not-yet-implemented",
    "full_lean_kernel_parity": "not-claimed",
    "lean_ecosystem_parity": "not-claimed",
}
EXPECTED_NEXT = (
    "M1: ordered group representation and singleton delegation under the existing "
    "mutual policy decline"
)


def _family(name: str, indices: int, constructors: list[str]) -> dict[str, Any]:
    return {
        "name": name,
        "num_params": 1,
        "num_indices": indices,
        "num_nested": 0,
        "is_rec": True,
        "is_reflexive": False,
        "constructors": constructors,
    }


def _recursor(
    name: str, indices: int, constructors: list[str], nfields: list[int]
) -> dict[str, Any]:
    return {
        "name": name,
        "num_params": 1,
        "num_indices": indices,
        "num_motives": 2,
        "num_minors": 4,
        "rule_constructors": constructors,
        "rule_nfields": nfields,
    }


PREFIX = "AxeyumMutualInductiveComputation."
EXPECTED_STREAMS = {
    "cross-family-computation": {
        "path": "docs/plan/fixtures/lean4export-v4.30-mutual-cross-computation.ndjson",
        "selected_root": PREFIX + "crossFamilyComputes",
        "sha256": "5013aff1165c8a50a63c54cd946ab2b489d0edfee7e0862bc53b061eabac0070",
        "bytes": 18_827,
        "records": 318,
        "max_rss_kib": [711_496, 711_984],
        "counts": (60, 4, 246, 7),
        "blockers": ["inductive-mutual"],
        "family_order": [PREFIX + "EvenTree", PREFIX + "OddTree"],
        "families": [
            _family(
                PREFIX + "EvenTree",
                0,
                [PREFIX + "EvenTree.leaf", PREFIX + "EvenTree.branch"],
            ),
            _family(
                PREFIX + "OddTree",
                0,
                [PREFIX + "OddTree.leaf", PREFIX + "OddTree.branch"],
            ),
        ],
        "wire_recursor_order": [PREFIX + "OddTree.rec", PREFIX + "EvenTree.rec"],
        "recursors": [
            _recursor(
                PREFIX + "OddTree.rec",
                0,
                [PREFIX + "OddTree.leaf", PREFIX + "OddTree.branch"],
                [0, 1],
            ),
            _recursor(
                PREFIX + "EvenTree.rec",
                0,
                [PREFIX + "EvenTree.leaf", PREFIX + "EvenTree.branch"],
                [1, 1],
            ),
        ],
    },
    "indexed-cross-family-computation": {
        "path": (
            "docs/plan/fixtures/lean4export-v4.30-mutual-indexed-computation.ndjson"
        ),
        "selected_root": PREFIX + "indexedCrossFamilyComputes",
        "sha256": "fe867639eeed25db9672730b092db32a49b79e82c6c59c386d9ff0e6a48b3787",
        "bytes": 21_455,
        "records": 374,
        "max_rss_kib": [712_284, 712_428],
        "counts": (72, 4, 290, 7),
        "blockers": ["inductive-mutual", "inductive-recursive-indexed"],
        "family_order": [PREFIX + "EvenVec", PREFIX + "OddVec"],
        "families": [
            _family(
                PREFIX + "EvenVec",
                1,
                [PREFIX + "EvenVec.nil", PREFIX + "EvenVec.step"],
            ),
            _family(
                PREFIX + "OddVec",
                1,
                [PREFIX + "OddVec.nil", PREFIX + "OddVec.step"],
            ),
        ],
        "wire_recursor_order": [PREFIX + "OddVec.rec", PREFIX + "EvenVec.rec"],
        "recursors": [
            _recursor(
                PREFIX + "OddVec.rec",
                1,
                [PREFIX + "OddVec.nil", PREFIX + "OddVec.step"],
                [0, 2],
            ),
            _recursor(
                PREFIX + "EvenVec.rec",
                1,
                [PREFIX + "EvenVec.nil", PREFIX + "EvenVec.step"],
                [0, 2],
            ),
        ],
    },
}


def sha256(path: Path) -> str:
    """Return one file's SHA-256."""

    return hashlib.sha256(path.read_bytes()).hexdigest()


def baseline_artifact_sha256(path: Path, key: str) -> str:
    """Hash an M0 artifact after removing its registered later-stage overlay."""

    if key != "construct_matrix":
        return sha256(path)
    registration = json.loads(path.read_text(encoding="utf-8"))
    registration.pop("tl2_13_update", None)
    encoded = (json.dumps(registration, indent=2) + "\n").encode()
    return hashlib.sha256(encoded).hexdigest()


def load_manifest() -> dict[str, Any]:
    """Load the committed M0 manifest."""

    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def _find_group(inventory: dict[str, Any], family_order: list[str]) -> dict[str, Any]:
    for group in inventory["inductive_groups"]:
        if [row["name"] for row in group["types"]] == family_order:
            return group
    return {}


def _observed_families(group: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "name": row["name"],
            "num_params": row["num_params"],
            "num_indices": row["num_indices"],
            "num_nested": row["num_nested"],
            "is_rec": row["is_rec"],
            "is_reflexive": row["is_reflexive"],
            "constructors": row["constructor_names"],
        }
        for row in group.get("types", [])
    ]


def _observed_recursors(group: dict[str, Any]) -> list[dict[str, Any]]:
    keys = (
        "name",
        "num_params",
        "num_indices",
        "num_motives",
        "num_minors",
        "rule_constructors",
        "rule_nfields",
    )
    return [{key: row[key] for key in keys} for row in group.get("recursors", [])]


def validate_manifest(data: dict[str, Any]) -> list[str]:
    """Return every fail-closed TL2.13 M0 registration violation."""

    failures: list[str] = []
    if set(data) != TOP_LEVEL_KEYS:
        failures.append("top-level fields drift or premature product observation")
    if data.get("schema") != SCHEMA:
        failures.append("schema drift")
    if data.get("stage") != "source-wire-frozen":
        failures.append("M0 stage must remain source-wire-frozen")
    if data.get("date") != "2026-07-22":
        failures.append("registration date drift")
    if data.get("decision") != (
        "docs/research/09-decisions/"
        "adr-0354-preregister-lean-mutual-inductive-groups.md"
    ):
        failures.append("decision path drift")
    if data.get("plan") != (
        "docs/plan/lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md"
    ):
        failures.append("plan path drift")
    if data.get("pins") != EXPECTED_PINS:
        failures.append("tool pin drift")
    if data.get("resource_policy") != EXPECTED_RESOURCES:
        failures.append("resource policy drift")
    if data.get("semantic_contract") != EXPECTED_SEMANTICS:
        failures.append("semantic contract drift")
    if data.get("claim_limits") != EXPECTED_CLAIMS:
        failures.append("claim limits drift or premature product credit")

    commands = data.get("commands", {})
    if commands.get("resource_runner_argv") != EXPECTED_RUNNER:
        failures.append("resource runner argv drift")
    if commands.get("lean_compile_argv") != EXPECTED_COMPILE:
        failures.append("Lean compile argv drift")
    if commands.get("lean4export_argv_template") != EXPECTED_EXPORT:
        failures.append("lean4export argv drift")
    if set(commands) != {
        "working_directory",
        "resource_runner_argv",
        "lean_compile_argv",
        "lean4export_argv_template",
    }:
        failures.append("command fields drift")

    baseline = data.get("baseline", {})
    if baseline != EXPECTED_BASELINE:
        failures.append("baseline identity/outcome contract drift")
    for key in ("construct_matrix", "mutual_stream", "singleton_control"):
        row = baseline.get(key, {})
        path = ROOT / str(row.get("path", ""))
        if not path.is_file():
            failures.append(f"baseline artifact missing: {key}")
        elif baseline_artifact_sha256(path, key) != row.get("sha256"):
            failures.append(f"baseline artifact hash drift: {key}")
        elif "bytes" in row and path.stat().st_size != row["bytes"]:
            failures.append(f"baseline artifact byte count drift: {key}")
        elif "records" in row and len(path.read_bytes().splitlines()) != row["records"]:
            failures.append(f"baseline artifact record count drift: {key}")

    source = data.get("source", {})
    if set(source) != {*EXPECTED_SOURCE, "roots"}:
        failures.append("source fields drift")
    for key, expected in EXPECTED_SOURCE.items():
        if source.get(key) != expected:
            failures.append(f"source {key} drift")
    if source.get("roots") != EXPECTED_ROOTS:
        failures.append("source roots or normal forms drift")
    source_path = ROOT / str(source.get("path", ""))
    if not source_path.is_file():
        failures.append("computation source missing")
    else:
        raw = source_path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != source.get("sha256"):
            failures.append("computation source hash drift")
        if len(raw) != source.get("bytes"):
            failures.append("computation source byte count drift")
        if len(raw.splitlines()) != source.get("lines"):
            failures.append("computation source line count drift")

    streams = data.get("streams", {})
    if tuple(streams) != tuple(EXPECTED_STREAMS):
        failures.append("stream population/order drift")
    total_bytes = 0
    for stream_id, expected in EXPECTED_STREAMS.items():
        row = streams.get(stream_id, {})
        path = ROOT / str(row.get("path", ""))
        if not path.is_file():
            failures.append(f"stream missing: {stream_id}")
            continue
        raw = path.read_bytes()
        observed = json.loads(json.dumps(census_bytes(raw, label=stream_id)))
        total_bytes += len(raw)
        for key in ("path", "selected_root", "sha256", "bytes", "records"):
            if row.get(key) != expected[key]:
                failures.append(f"stream {key} drift: {stream_id}")
        if observed["sha256"] != expected["sha256"]:
            failures.append(f"stream hash drift: {stream_id}")
        if observed["bytes"] != expected["bytes"]:
            failures.append(f"stream byte count drift: {stream_id}")
        if observed["records"] != expected["records"]:
            failures.append(f"stream record count drift: {stream_id}")
        if not observed["declaration_names"] or observed["declaration_names"][-1] != expected["selected_root"]:
            failures.append(f"selected root is not final declaration: {stream_id}")
        if row.get("export_runs") != 2 or row.get("byte_identical") is not True:
            failures.append(f"stream reproduction drift: {stream_id}")
        if row.get("max_rss_kib") != expected["max_rss_kib"]:
            failures.append(f"stream resource observation drift: {stream_id}")

        registered = row.get("inventory", {})
        observed_counts = tuple(
            observed[key] for key in ("names", "levels", "exprs", "decls")
        )
        registered_counts = tuple(
            registered.get(key)
            for key in ("names", "levels", "expressions", "declaration_records")
        )
        if observed_counts != expected["counts"] or registered_counts != expected["counts"]:
            failures.append(f"inventory count drift: {stream_id}")
        for key in ("format", "lean", "lean_githash"):
            if registered.get(key) != observed[key]:
                failures.append(f"inventory {key} drift: {stream_id}")
        if registered.get("blockers") != expected["blockers"] or observed["blockers"] != expected["blockers"]:
            failures.append(f"blocker inventory drift: {stream_id}")

        if registered.get("family_order") != expected["family_order"]:
            failures.append(f"family order drift: {stream_id}")
        group = _find_group(observed, expected["family_order"])
        if not group:
            failures.append(f"target mutual group missing: {stream_id}")
        else:
            if _observed_families(group) != expected["families"]:
                failures.append(f"target family metadata drift: {stream_id}")
            if _observed_recursors(group) != expected["recursors"]:
                failures.append(f"target recursor metadata/order drift: {stream_id}")
        if registered.get("families") != expected["families"]:
            failures.append(f"registered family metadata drift: {stream_id}")
        if registered.get("wire_recursor_order") != expected["wire_recursor_order"]:
            failures.append(f"registered wire recursor order drift: {stream_id}")
        if registered.get("recursors") != expected["recursors"]:
            failures.append(f"registered recursor metadata drift: {stream_id}")

    if any(
        row.get("bytes", EXPECTED_RESOURCES["per_stream_max_bytes"] + 1)
        > EXPECTED_RESOURCES["per_stream_max_bytes"]
        for row in streams.values()
    ):
        failures.append("per-stream retention bound exceeded")
    if total_bytes > EXPECTED_RESOURCES["aggregate_stream_max_bytes"]:
        failures.append("aggregate retention bound exceeded")

    case_ids = tuple(data.get("case_ids", ()))
    if case_ids != EXPECTED_CASE_IDS:
        failures.append("case population/order drift")
    if len(case_ids) != len(set(case_ids)):
        failures.append("case IDs must be unique")
    mutation_ids = tuple(data.get("mutation_ids", ()))
    if mutation_ids != EXPECTED_MUTATION_IDS:
        failures.append("mutation population/order drift")
    if len(mutation_ids) != len(set(mutation_ids)):
        failures.append("mutation IDs must be unique")
    if data.get("generated_grammar") != EXPECTED_GRAMMAR:
        failures.append("generated grammar contract drift")
    if data.get("mandatory_controls") != EXPECTED_CONTROLS:
        failures.append("mandatory control contract drift")
    for key in (
        "recursive_manifest",
        "strict_positivity_manifest",
        "official_construct_matrix",
    ):
        if not (ROOT / str(data.get("mandatory_controls", {}).get(key, ""))).is_file():
            failures.append(f"mandatory control missing: {key}")
    if tuple(data.get("stop_condition_ids", ())) != EXPECTED_STOP_IDS:
        failures.append("stop-condition population/order drift")
    if data.get("next") != EXPECTED_NEXT:
        failures.append("next milestone drift")
    return failures


def main() -> int:
    """CLI entry point."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate committed bytes")
    parser.parse_args()
    try:
        failures = validate_manifest(load_manifest())
    except (OSError, json.JSONDecodeError, UnicodeDecodeError) as error:
        print(f"lean mutual inductive M0 invalid: {error}", file=sys.stderr)
        return 1
    if failures:
        for failure in failures:
            print(f"lean mutual inductive M0 invalid: {failure}", file=sys.stderr)
        return 1
    print(
        "lean mutual inductive M0 source/wire freeze valid: "
        "2 groups, 2 roots, 40282 bytes, no Axeyum product observations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
