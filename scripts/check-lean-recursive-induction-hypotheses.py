#!/usr/bin/env python3
"""Validate the TL2.12 M0 source/wire freeze without product credit."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = str(ROOT / "scripts")
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)

from prototype_lean4export_census import census_bytes  # noqa: E402


MANIFEST = ROOT / "docs" / "plan" / "lean-recursive-induction-hypotheses-v1.json"
SCHEMA = "axeyum-lean-recursive-induction-hypotheses-v1"
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
    "claim_limits",
    "semantic_contract",
    "source",
    "streams",
    "case_ids",
    "mutation_ids",
    "generated_grammar",
    "mandatory_controls",
    "stop_condition_ids",
    "next_milestone",
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
    "rust_jobs": 2,
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
    "AxeyumRecursiveIHComputation.olean",
    "AxeyumRecursiveIHComputation.lean",
]
EXPECTED_EXPORT = [
    "/usr/bin/time",
    "-v",
    "env",
    "PATH=<pinned-lean-bin>:$PATH",
    "LEAN_PATH=.",
    "<pinned-lean4export>",
    "AxeyumRecursiveIHComputation",
    "--",
    "<selected-root>",
]
EXPECTED_CLAIMS = {
    "official_source_compilation": "passed-twice",
    "official_export_determinism": "passed-twice-per-root",
    "official_wire_inventory": "frozen",
    "axeyum_import": "not-run-on-new-streams",
    "axeyum_admission": "not-run-on-new-streams",
    "axeyum_computation": "not-run-on-new-streams",
    "full_lean_kernel_parity": "not-claimed",
    "lean_ecosystem_parity": "not-claimed",
}
EXPECTED_SEMANTICS = {
    "recursive_field": "u : Pi xs, I params indices",
    "induction_hypothesis": "Pi xs, motive indices (u xs)",
    "rule_argument": "fun xs => I.rec params motive minors indices (u xs)",
    "minor_order": (
        "all constructor fields in source order, then IHs in recursive-field order"
    ),
    "classifier": (
        "one WHNF telescope-tail path for minor types and rule right-hand sides"
    ),
    "metadata_authority": (
        "field structure and kernel checking; isReflexive is descriptive only"
    ),
    "direct_control": "empty telescope and empty index vector",
}
EXPECTED_BASELINE = {
    "revision": "69c4d89d05940ca0de420093173ad0d93613e822",
    "result": "docs/plan/lean-official-construct-matrix-product-2026-07-22.md",
    "direct_recursive_control": {
        "path": "docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson",
        "sha256": "91df1e44219483b213000b94b06016f9569dc648d0680d9ae91ff3198817db08",
        "registered_outcome": "completed-import",
    },
    "recursive_indexed": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-construct-matrix-recursive-indexed.ndjson"
        ),
        "sha256": "df1e82fa72eac9f2a37cdf3b0eb8044f118489c51f76ab14b9af06c3f4cf11de",
        "registered_outcome": "KernelError::RecursiveIndexedNotSupported",
    },
    "reflexive_higher_order": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-construct-matrix-reflexive-higher-order.ndjson"
        ),
        "sha256": "a2dc21e61e6938bd5eb5d8c4032c7d6197e312c7a617b8bd33388f2e46db0ec3",
        "registered_outcome": "ImportError::Unsupported(inductive-reflexive)",
    },
}
EXPECTED_CASE_IDS = (
    "direct-control",
    "vector-direct-indexed",
    "higher-order-zero-index",
    "acc-indexed-dependent",
    "two-binder-dependent",
    "mixed-fields",
    "multiple-recursive",
    "implicit-telescope",
    "reducible-wrapper",
    "prop-acc",
    "wrong-tail-params",
    "family-in-domain",
    "family-in-index",
    "nested-foreign-head",
)
EXPECTED_MUTATION_IDS = (
    "omit-duplicate-reorder-ih",
    "ih-before-fields",
    "drop-reorder-index",
    "constructor-index-for-recursive-index",
    "motive-on-unapplied-field",
    "nested-lambda-or-argument-order",
    "nested-binder-type-or-info",
    "neighbor-field-recursion",
    "wrong-motive-or-universe",
    "official-recursor-type-minor-rule-nfields",
    "reflexive-metadata-nonauthority",
    "late-failure-no-publication",
)
EXPECTED_STOP_IDS = (
    "lean-rule-disagreement",
    "direct-recursive-identity-drift",
    "positivity-classification-drift",
    "classifier-reconstruction-disagreement",
    "self-checks-but-official-differs",
    "official-import-without-recursor-comparison",
    "constructor-witness-promoted-to-computation",
    "failure-publishes-environment",
    "requires-multiple-family-motives",
    "nested-unsafe-malformed-admitted",
    "generated-summary-invalid",
    "resource-cap-exceeded-or-killed",
    "unrelated-dirty-overlap",
)
EXPECTED_ROOTS = (
    {
        "id": "vector-computation",
        "selected_root": "AxeyumRecursiveIHComputation.vectorHeightComputes",
        "recursor_consumer": "AxeyumRecursiveIHComputation.vectorHeight",
        "expected_normal_form": "MiniNat.succ MiniNat.zero",
    },
    {
        "id": "acc-computation",
        "selected_root": "AxeyumRecursiveIHComputation.accPropertyComputes",
        "recursor_consumer": "AxeyumRecursiveIHComputation.accProperty",
        "expected_normal_form": "True",
    },
)
EXPECTED_SOURCE_SCALARS = {
    "path": "docs/plan/fixtures/lean-v4.30-recursive-ih-computation.lean",
    "sha256": "ebf95e789906c05a27db5eb55b29a8fe7c2429969712099b6aca4905dc88b06d",
    "bytes": 1_422,
    "lines": 48,
    "module": "AxeyumRecursiveIHComputation",
    "compile_runs": 2,
    "compile_exit_statuses": [0, 0],
    "compile_max_rss_kib": [462_868, 462_912],
}
EXPECTED_GRAMMAR = {
    "seed_policy": "fixed and committed at M2 before the first generated run",
    "minimum_unique_cases": 512,
    "recursive_fields": "0..3 among 0..5 total fields",
    "telescope_depth": "0..3",
    "profiles": ["0p0i", "1p0i", "1p1i", "2p1i"],
    "result_sorts": ["Prop", "Type"],
    "binder_info": ["explicit", "implicit", "strict-implicit"],
    "required_repetitions": 2,
    "summary_identity": "byte-identical",
}
EXPECTED_CONTROLS = {
    "strict_positivity_manifest": "docs/plan/lean-strict-positivity-v1.json",
    "strict_positivity_generated_cases": 840,
    "official_construct_matrix": "docs/plan/lean-official-construct-matrix-v1.json",
    "transactional_import": "CompletedImport only after full-stream success",
    "direct_recursive_identity": (
        "must be registered at M1 before admission widens"
    ),
}
EXPECTED_NEXT = (
    "M1: shared WHNF recursive-field representation under existing feature declines"
)
STREAM_KEYS = {
    "path",
    "selected_root",
    "sha256",
    "bytes",
    "records",
    "export_runs",
    "byte_identical",
    "max_rss_kib",
    "inventory",
}
INVENTORY_KEYS = {
    "format",
    "lean",
    "lean_githash",
    "names",
    "levels",
    "exprs",
    "decls",
    "blockers",
    "target_inductive",
    "target_recursor",
}
EXPECTED_STREAMS = {
    "vector-computation": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-recursive-ih-vector-computation.ndjson"
        ),
        "selected_root": "AxeyumRecursiveIHComputation.vectorHeightComputes",
        "sha256": "1ab5a38b50d4d2c7ba01ef2831bb5af5d3c56ce1b9879c1942070519a9f6df19",
        "bytes": 15_944,
        "records": 284,
        "max_rss_kib": [703_092, 706_180],
        "counts": (60, 4, 211, 8),
        "blockers": ["inductive-recursive-indexed"],
        "target_inductive": {
            "name": "AxeyumRecursiveIHComputation.MiniVector",
            "num_params": 1,
            "num_indices": 1,
            "num_nested": 0,
            "is_rec": True,
            "is_reflexive": False,
        },
        "target_recursor": {
            "name": "AxeyumRecursiveIHComputation.MiniVector.rec",
            "num_params": 1,
            "num_indices": 1,
            "num_motives": 1,
            "num_minors": 2,
            "rule_nfields": [0, 3],
        },
    },
    "acc-computation": {
        "path": (
            "docs/plan/fixtures/"
            "lean4export-v4.30-recursive-ih-acc-computation.ndjson"
        ),
        "selected_root": "AxeyumRecursiveIHComputation.accPropertyComputes",
        "sha256": "3cb06283f1e757d79d28335dfe77ccd00231a8d323c2310dddced6473933c003",
        "bytes": 17_722,
        "records": 314,
        "max_rss_kib": [704_284, 705_276],
        "counts": (67, 3, 232, 11),
        "blockers": ["inductive-recursive-indexed", "inductive-reflexive"],
        "target_inductive": {
            "name": "AxeyumRecursiveIHComputation.MiniAcc",
            "num_params": 2,
            "num_indices": 1,
            "num_nested": 0,
            "is_rec": True,
            "is_reflexive": True,
        },
        "target_recursor": {
            "name": "AxeyumRecursiveIHComputation.MiniAcc.rec",
            "num_params": 2,
            "num_indices": 1,
            "num_motives": 1,
            "num_minors": 1,
            "rule_nfields": [2],
        },
    },
}


def sha256(path: Path) -> str:
    """Return the lowercase SHA-256 digest of *path*."""

    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_manifest() -> dict[str, Any]:
    """Load the committed M0 registration."""

    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def _find_inductive(inventory: dict[str, Any], name: str) -> dict[str, Any] | None:
    for group in inventory["inductive_groups"]:
        for inductive in group["types"]:
            if inductive["name"] == name:
                return inductive
    return None


def _find_recursor(inventory: dict[str, Any], name: str) -> dict[str, Any] | None:
    for group in inventory["inductive_groups"]:
        for recursor in group["recursors"]:
            if recursor["name"] == name:
                return recursor
    return None


def _subset(row: dict[str, Any] | None, keys: Any) -> dict[str, Any] | None:
    if row is None:
        return None
    return {key: row.get(key) for key in keys}


def validate_manifest(data: dict[str, Any]) -> list[str]:
    """Return every fail-closed M0 registration violation."""

    failures: list[str] = []
    if set(data) != TOP_LEVEL_KEYS:
        failures.append("top-level fields drift")
    if data.get("schema") != SCHEMA:
        failures.append("schema drift")
    if data.get("stage") != "source-wire-frozen":
        failures.append("M0 stage must remain source-wire-frozen")
    if data.get("date") != "2026-07-22":
        failures.append("registration date drift")
    if data.get("decision") != (
        "docs/research/09-decisions/"
        "adr-0353-preregister-lean-recursive-induction-hypotheses.md"
    ):
        failures.append("decision path drift")
    if data.get("plan") != (
        "docs/plan/"
        "lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md"
    ):
        failures.append("plan path drift")
    if data.get("pins") != EXPECTED_PINS:
        failures.append("tool pin drift")
    if data.get("resource_policy") != EXPECTED_RESOURCES:
        failures.append("resource policy drift")

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

    if data.get("claim_limits") != EXPECTED_CLAIMS:
        failures.append("claim limits drift or product credit appeared")
    if data.get("semantic_contract") != EXPECTED_SEMANTICS:
        failures.append("semantic contract drift")

    baseline = data.get("baseline", {})
    if baseline != EXPECTED_BASELINE:
        failures.append("baseline identity/outcome contract drift")
    if not (ROOT / EXPECTED_BASELINE["result"]).is_file():
        failures.append("baseline result document missing")
    for key in (
        "direct_recursive_control",
        "recursive_indexed",
        "reflexive_higher_order",
    ):
        row = baseline.get(key, {})
        path = ROOT / str(row.get("path", ""))
        if not path.is_file():
            failures.append(f"baseline fixture missing: {key}")
        elif sha256(path) != row.get("sha256"):
            failures.append(f"baseline fixture hash drift: {key}")

    source = data.get("source", {})
    if set(source) != {*EXPECTED_SOURCE_SCALARS, "roots"}:
        failures.append("computation source fields drift")
    for key, expected_value in EXPECTED_SOURCE_SCALARS.items():
        if source.get(key) != expected_value:
            failures.append(f"computation source {key} drift")
    source_path = ROOT / str(source.get("path", ""))
    if not source_path.is_file():
        failures.append("computation source missing")
    else:
        source_bytes = source_path.read_bytes()
        if hashlib.sha256(source_bytes).hexdigest() != source.get("sha256"):
            failures.append("computation source hash drift")
        if len(source_bytes) != source.get("bytes"):
            failures.append("computation source byte count drift")
        if len(source_bytes.decode("utf-8").splitlines()) != source.get("lines"):
            failures.append("computation source line count drift")
    if tuple(source.get("roots", ())) != EXPECTED_ROOTS:
        failures.append("computation roots or normal forms drift")

    streams = data.get("streams", {})
    if tuple(streams) != tuple(EXPECTED_STREAMS):
        failures.append("stream population/order drift")
    total_bytes = 0
    for stream_id, expected in EXPECTED_STREAMS.items():
        row = streams.get(stream_id, {})
        if set(row) != STREAM_KEYS:
            failures.append(f"stream fields drift: {stream_id}")
        if set(row.get("inventory", {})) != INVENTORY_KEYS:
            failures.append(f"registered inventory fields drift: {stream_id}")
        path = ROOT / str(row.get("path", ""))
        if not path.is_file():
            failures.append(f"stream missing: {stream_id}")
            continue
        raw = path.read_bytes()
        inventory = json.loads(json.dumps(census_bytes(raw, label=stream_id)))
        total_bytes += len(raw)
        if row.get("path") != expected["path"]:
            failures.append(f"stream path drift: {stream_id}")
        if row.get("sha256") != expected["sha256"] or inventory["sha256"] != expected["sha256"]:
            failures.append(f"stream hash drift: {stream_id}")
        if row.get("bytes") != expected["bytes"] or inventory["bytes"] != expected["bytes"]:
            failures.append(f"stream byte count drift: {stream_id}")
        if row.get("records") != expected["records"] or inventory["records"] != expected["records"]:
            failures.append(f"stream record count drift: {stream_id}")
        if row.get("selected_root") != expected["selected_root"]:
            failures.append(f"selected root drift: {stream_id}")
        if not inventory["declaration_names"] or inventory["declaration_names"][-1] != expected["selected_root"]:
            failures.append(f"selected root is not final declaration: {stream_id}")
        if row.get("export_runs") != 2 or row.get("byte_identical") is not True:
            failures.append(f"export repetition/identity drift: {stream_id}")
        if row.get("max_rss_kib") != expected["max_rss_kib"]:
            failures.append(f"export resource observation drift: {stream_id}")

        registered_inventory = row.get("inventory", {})
        counts = tuple(
            inventory[key] for key in ("names", "levels", "exprs", "decls")
        )
        if counts != expected["counts"]:
            failures.append(f"independent inventory count drift: {stream_id}")
        for key in ("format", "lean", "lean_githash"):
            if registered_inventory.get(key) != inventory[key]:
                failures.append(f"registered inventory {key} drift: {stream_id}")
        if registered_inventory.get("blockers") != expected["blockers"] or inventory["blockers"] != expected["blockers"]:
            failures.append(f"blocker inventory drift: {stream_id}")
        registered_counts = tuple(
            registered_inventory.get(key) for key in ("names", "levels", "exprs", "decls")
        )
        if registered_counts != expected["counts"]:
            failures.append(f"registered inventory count drift: {stream_id}")

        target_inductive = expected["target_inductive"]
        observed_inductive = _subset(
            _find_inductive(inventory, target_inductive["name"]), target_inductive
        )
        if row.get("inventory", {}).get("target_inductive") != target_inductive or observed_inductive != target_inductive:
            failures.append(f"target inductive metadata drift: {stream_id}")
        target_recursor = expected["target_recursor"]
        observed_recursor = _subset(
            _find_recursor(inventory, target_recursor["name"]), target_recursor
        )
        if row.get("inventory", {}).get("target_recursor") != target_recursor or observed_recursor != target_recursor:
            failures.append(f"target recursor metadata drift: {stream_id}")

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

    grammar = data.get("generated_grammar", {})
    if grammar != EXPECTED_GRAMMAR:
        failures.append("generated grammar contract drift")

    controls = data.get("mandatory_controls", {})
    if controls != EXPECTED_CONTROLS:
        failures.append("mandatory control contract drift")
    for key in ("strict_positivity_manifest", "official_construct_matrix"):
        if not (ROOT / str(controls.get(key, ""))).is_file():
            failures.append(f"mandatory control missing: {key}")
    if tuple(data.get("stop_condition_ids", ())) != EXPECTED_STOP_IDS:
        failures.append("stop-condition population/order drift")
    if data.get("next_milestone") != EXPECTED_NEXT:
        failures.append("next milestone drift")

    forbidden = {
        "axeyum_product_observations",
        "kernel_results",
        "importer_results",
        "completed_imports",
        "axeyum_computation_results",
        "generated_summary",
    }
    if forbidden.intersection(data):
        failures.append("M0 registration contains premature Axeyum observations")

    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_PINS["lean"]["toolchain"]:
        failures.append("repository lean-toolchain drift")
    return failures


def main() -> int:
    """CLI entry point."""

    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.parse_args()
    failures = validate_manifest(load_manifest())
    if failures:
        for failure in failures:
            print(f"lean recursive IH M0: {failure}", file=sys.stderr)
        return 1
    total = sum(row["bytes"] for row in EXPECTED_STREAMS.values())
    print(
        "lean recursive IH M0 source/wire freeze valid: "
        f"{len(EXPECTED_ROOTS)} roots, {total} bytes, "
        "no Axeyum product observations"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
