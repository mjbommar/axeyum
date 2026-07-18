#!/usr/bin/env python3
"""Compare repeated, same-revision Glaurung rewrite ablation artifacts.

Each ablation artifact must differ from its paired base artifact only by
disabling one named default rewrite rule (and the resulting configuration
identity). Deltas are reported as ``ablation - base``: positive work/time means
the enabled base rule avoided that work/time. Structural deltas are exact;
timing deltas require process-level repetitions and retain every sample.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import statistics
import tempfile
from pathlib import Path
from typing import Any, NoReturn, Sequence


SOURCE_ARTIFACT_VERSION = 32
COMPARISON_VERSION = 1
STRUCTURAL_METRICS = (
    "term_bits_lowered",
    "aig_and_requests",
    "aig_nodes",
    "cnf_variables",
    "cnf_clauses",
)
TIMING_METRICS = (
    "cold_total_ms",
    "rewrite_ms",
    "bit_blast_ms",
    "cnf_encode_ms",
    "solve_ms",
)


class ComparisonError(ValueError):
    """An artifact is invalid or an ablation pair is not comparable."""


def fail(message: str) -> NoReturn:
    raise ComparisonError(message)


def require_mapping(value: Any, location: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        fail(f"{location} must be a JSON object")
    return value


def require_list(value: Any, location: str) -> list[Any]:
    if not isinstance(value, list):
        fail(f"{location} must be a JSON array")
    return value


def require_string(value: Any, location: str) -> str:
    if not isinstance(value, str) or not value:
        fail(f"{location} must be a non-empty string")
    return value


def require_int(value: Any, location: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        fail(f"{location} must be an integer")
    return value


def require_number(value: Any, location: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        fail(f"{location} must be a number")
    result = float(value)
    if not math.isfinite(result):
        fail(f"{location} must be finite")
    return result


def load_json(path: Path) -> tuple[dict[str, Any], str]:
    try:
        data = path.read_bytes()
        value = json.loads(
            data,
            parse_constant=lambda token: fail(
                f"parse {path}: non-finite JSON number {token}"
            ),
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"read/parse {path}: {error}")
    return require_mapping(value, str(path)), "sha256:" + hashlib.sha256(data).hexdigest()


def distribution(values: Sequence[float]) -> dict[str, Any]:
    ordered = sorted(values)

    def percentile(percent: int) -> float:
        rank = max(0, math.ceil(percent * len(ordered) / 100) - 1)
        return ordered[min(rank, len(ordered) - 1)]

    return {
        "samples": list(values),
        "min": ordered[0],
        "p50": percentile(50),
        "p95": percentile(95),
        "max": ordered[-1],
        "mean": statistics.fmean(ordered),
        "sample_standard_deviation": (
            statistics.stdev(ordered) if len(ordered) > 1 else 0.0
        ),
    }


def validate_artifact(value: dict[str, Any], path: Path) -> dict[str, Any]:
    if require_int(value.get("version"), f"{path}: version") != SOURCE_ARTIFACT_VERSION:
        fail(f"{path}: expected artifact version {SOURCE_ARTIFACT_VERSION}")
    config = require_mapping(value.get("config"), f"{path}: config")
    if config.get("require_reproducible_run") is not True:
        fail(f"{path}: require_reproducible_run must be true")
    if require_int(config.get("jobs"), f"{path}: config.jobs") != 1:
        fail(f"{path}: config.jobs must be 1")
    if config.get("compare_z3") is not True or config.get("require_in_process_z3") is not True:
        fail(f"{path}: an in-process Z3 comparison is required")
    if config.get("require_deterministic_resources") is not True:
        fail(f"{path}: deterministic resource limits are required")
    if require_string(config.get("backend_kind"), f"{path}: backend_kind") != "sat-bv":
        fail(f"{path}: backend_kind must be sat-bv")
    if require_string(config.get("logic"), f"{path}: logic") != "QF_BV":
        fail(f"{path}: logic must be QF_BV")
    if not math.isclose(
        require_number(
            config.get("min_decided_percent"), f"{path}: min_decided_percent"
        ),
        100.0,
        rel_tol=0.0,
        abs_tol=1e-12,
    ):
        fail(f"{path}: min_decided_percent must be 100")
    experiment = require_mapping(config.get("experiment"), f"{path}: experiment")
    source = require_mapping(experiment.get("source"), f"{path}: source")
    if source.get("dirty") is not False:
        fail(f"{path}: source must be clean")
    require_string(source.get("revision"), f"{path}: source.revision")
    require_string(experiment.get("environment_hash"), f"{path}: environment_hash")

    summary = require_mapping(value.get("summary"), f"{path}: summary")
    files = require_int(summary.get("files"), f"{path}: summary.files")
    if require_int(summary.get("decided"), f"{path}: summary.decided") != files:
        fail(f"{path}: every query must be decided")
    if not math.isclose(
        require_number(
            summary.get("decided_percent"), f"{path}: summary.decided_percent"
        ),
        100.0,
        rel_tol=0.0,
        abs_tol=1e-12,
    ):
        fail(f"{path}: summary.decided_percent must be 100")
    for field in ("errors", "disagree", "model_replay_failures"):
        if require_int(summary.get(field), f"{path}: summary.{field}") != 0:
            fail(f"{path}: summary.{field} must be zero")
    for section in ("oracle", "manifest"):
        gate = require_mapping(summary.get(section), f"{path}: summary.{section}")
        if require_int(gate.get("compared"), f"{path}: {section}.compared") != files:
            fail(f"{path}: every query must be {section}-compared")
        if require_int(gate.get("agree"), f"{path}: {section}.agree") != files:
            fail(f"{path}: every query must {section}-agree")
        if require_int(gate.get("disagree"), f"{path}: {section}.disagree") != 0:
            fail(f"{path}: {section}.disagree must be zero")

    instances = require_list(value.get("instances"), f"{path}: instances")
    if len(instances) != files:
        fail(f"{path}: instance count does not match summary.files")
    by_file: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(instances):
        instance = require_mapping(raw, f"{path}: instances[{index}]")
        file = require_string(instance.get("file"), f"{path}: instances[{index}].file")
        if file in by_file:
            fail(f"{path}: duplicate instance path {file}")
        oracle = require_mapping(instance.get("oracle"), f"{path}: {file}.oracle")
        manifest = require_mapping(
            instance.get("corpus_manifest"), f"{path}: {file}.corpus_manifest"
        )
        if oracle.get("decision_agrees") is not True or manifest.get("decision_agrees") is not True:
            fail(f"{path}: {file} is not oracle/manifest agreed")
        by_file[file] = instance
    return {"config": config, "instances": by_file}


def normalized_config(config: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(config)
    result.pop("config_hash", None)
    result.pop("rewrite", None)
    return result


def validate_pair(
    base: dict[str, Any], ablation: dict[str, Any], base_path: Path, ablation_path: Path
) -> str:
    if normalized_config(base["config"]) != normalized_config(ablation["config"]):
        fail(f"{base_path} and {ablation_path}: configuration drift outside rewrite selection")
    base_rewrite = require_mapping(base["config"].get("rewrite"), f"{base_path}: rewrite")
    ablation_rewrite = require_mapping(
        ablation["config"].get("rewrite"), f"{ablation_path}: rewrite"
    )
    if base_rewrite.get("mode") != "default" or ablation_rewrite.get("mode") != "default":
        fail("rewrite ablation requires default rewrite mode")
    if require_list(base_rewrite.get("disabled_rule_ids"), "base disabled rules"):
        fail(f"{base_path}: base artifact must not disable rules")
    disabled = require_list(ablation_rewrite.get("disabled_rule_ids"), "ablation disabled rules")
    if len(disabled) != 1:
        fail(f"{ablation_path}: ablation must disable exactly one rule")
    rule = require_string(disabled[0], f"{ablation_path}: disabled rule")
    base_enabled = require_list(base_rewrite.get("enabled_rule_ids"), "base enabled rules")
    ablation_enabled = require_list(
        ablation_rewrite.get("enabled_rule_ids"), "ablation enabled rules"
    )
    if rule not in base_enabled:
        fail(f"{ablation_path}: disabled rule is not in the base manifest")
    if ablation_enabled != [item for item in base_enabled if item != rule]:
        fail(f"{ablation_path}: enabled rules are not base minus {rule}")
    if base_rewrite.get("base_rule_set") != ablation_rewrite.get("base_rule_set"):
        fail(f"{ablation_path}: base_rule_set drift")
    if set(base["instances"]) != set(ablation["instances"]):
        fail(f"{base_path} and {ablation_path}: instance path sets differ")
    for file, base_instance in base["instances"].items():
        candidate = ablation["instances"][file]
        if base_instance.get("outcome") != candidate.get("outcome"):
            fail(f"{file}: solver outcome changed under ablation")
        if base_instance["corpus_manifest"].get("family") != candidate["corpus_manifest"].get("family"):
            fail(f"{file}: corpus family changed under ablation")
    return rule


def metric(instance: dict[str, Any], name: str) -> float:
    if name == "cold_total_ms":
        return require_number(instance.get(name), name)
    if name == "rewrite_ms":
        rewrite = require_mapping(instance.get("rewrite"), "instance.rewrite")
        return require_number(rewrite.get("elapsed_ms"), "rewrite.elapsed_ms")
    if name == "solve_ms":
        return require_number(instance.get(name), name)
    stats = require_mapping(instance.get("backend_stats"), "instance.backend_stats")
    return require_number(stats.get(name), f"backend_stats.{name}")


def compare(base_paths: Sequence[Path], ablation_paths: Sequence[Path]) -> dict[str, Any]:
    if len(base_paths) != len(ablation_paths) or not base_paths:
        fail("base and ablation lists must have the same non-zero length")
    if len(base_paths) < 2:
        fail("timing attribution requires at least two process-level repetitions")

    pairs = []
    hashes = []
    rule_id: str | None = None
    reference_base_config = None
    reference_ablation_config = None
    affected_signature = None
    for base_path, ablation_path in zip(base_paths, ablation_paths, strict=True):
        base_raw, base_hash = load_json(base_path)
        ablation_raw, ablation_hash = load_json(ablation_path)
        base = validate_artifact(base_raw, base_path)
        ablation = validate_artifact(ablation_raw, ablation_path)
        pair_rule = validate_pair(base, ablation, base_path, ablation_path)
        if rule_id is None:
            rule_id = pair_rule
            reference_base_config = base["config"]
            reference_ablation_config = ablation["config"]
        elif pair_rule != rule_id:
            fail(f"{ablation_path}: disabled rule differs across repetitions")
        if base["config"] != reference_base_config or ablation["config"] != reference_ablation_config:
            fail("configuration or environment drift across repetitions")

        affected = []
        family_counts: dict[str, int] = {}
        applications = 0
        for file, instance in base["instances"].items():
            rewrite = require_mapping(instance.get("rewrite"), f"{file}: rewrite")
            counts = require_mapping(rewrite.get("rule_counts"), f"{file}: rule_counts")
            count = counts.get(pair_rule, 0)
            count_number = require_int(count, f"{file}: rule count")
            if count_number > 0:
                affected.append(file)
                applications += count_number
                family = require_string(
                    instance["corpus_manifest"].get("family"), f"{file}: family"
                )
                family_counts[family] = family_counts.get(family, 0) + 1
        signature = (tuple(affected), tuple(sorted(family_counts.items())), applications)
        if affected_signature is None:
            affected_signature = signature
        elif signature != affected_signature:
            fail("affected query/family/application set drifted across repetitions")
        if not affected:
            fail(f"{pair_rule}: rule did not fire in the base artifact")

        structural = {}
        timing_affected = {}
        timing_whole = {}
        for name in STRUCTURAL_METRICS:
            structural[name] = sum(
                metric(ablation["instances"][file], name)
                - metric(base["instances"][file], name)
                for file in affected
            )
        for name in TIMING_METRICS:
            timing_affected[name] = sum(
                metric(ablation["instances"][file], name)
                - metric(base["instances"][file], name)
                for file in affected
            )
            timing_whole[name] = sum(
                metric(ablation["instances"][file], name)
                - metric(base["instances"][file], name)
                for file in base["instances"]
            )
        pairs.append(
            {
                "structural": structural,
                "timing_affected": timing_affected,
                "timing_whole": timing_whole,
            }
        )
        hashes.append({"base": base_hash, "ablation": ablation_hash})

    assert rule_id is not None and affected_signature is not None
    affected, family_items, applications = affected_signature
    structural_report = {
        name: distribution([pair["structural"][name] for pair in pairs])
        for name in STRUCTURAL_METRICS
    }
    timing_report = {
        scope: {
            name: distribution([pair[scope][name] for pair in pairs])
            for name in TIMING_METRICS
        }
        for scope in ("timing_affected", "timing_whole")
    }
    return {
        "version": COMPARISON_VERSION,
        "source_artifact_version": SOURCE_ARTIFACT_VERSION,
        "delta_direction": "ablation_minus_base; positive means the enabled base rule avoided work/time",
        "rule_id": rule_id,
        "repetitions": len(pairs),
        "source_revision": reference_base_config["experiment"]["source"]["revision"],
        "environment_hash": reference_base_config["experiment"]["environment_hash"],
        "corpus_hash": reference_base_config["corpus_hash"],
        "manifest_hash": reference_base_config["corpus_manifest"]["content_hash"],
        "affected": {
            "instances": len(affected),
            "families": dict(family_items),
            "applications": applications,
        },
        "validity": {
            "all_queries_decided": True,
            "oracle_and_manifest_agreement": True,
            "zero_errors_disagreements_or_replay_failures": True,
            "same_revision_environment_corpus_and_non_rewrite_config": True,
        },
        "artifact_hashes": hashes,
        "structural_affected_ablation_minus_base": structural_report,
        "timing_affected_ablation_minus_base_ms": timing_report["timing_affected"],
        "timing_whole_corpus_ablation_minus_base_ms": timing_report["timing_whole"],
    }


def atomic_write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, delete=False
    ) as temporary:
        json.dump(value, temporary, indent=2, sort_keys=True)
        temporary.write("\n")
        temporary_path = Path(temporary.name)
    temporary_path.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, nargs="+", required=True)
    parser.add_argument("--ablation", type=Path, nargs="+", required=True)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    try:
        result = compare(args.base, args.ablation)
        if args.out is not None:
            atomic_write_json(args.out, result)
        else:
            print(json.dumps(result, indent=2, sort_keys=True))
    except ComparisonError as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
