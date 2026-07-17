#!/usr/bin/env python3
"""Join fair Glaurung timings to auditable query-shape features.

This is descriptive attribution, not a causal classifier. It consumes one or
more committed paired-analysis reports, revalidates every referenced raw trace,
and emits per-occurrence rows plus driver/feature summaries. Ratios are paired
geometric means across repetitions; values greater than one favor Axeyum.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import math
import pathlib
import re
import statistics
import sys
from collections import Counter
from typing import Any, Iterable, Sequence


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
PAIRED_SCRIPT = SCRIPT_DIR / "analyze-glaurung-paired-traces.py"
PAIRED_SPEC = importlib.util.spec_from_file_location("glaurung_paired", PAIRED_SCRIPT)
assert PAIRED_SPEC is not None and PAIRED_SPEC.loader is not None
paired = importlib.util.module_from_spec(PAIRED_SPEC)
sys.modules[PAIRED_SPEC.name] = paired
PAIRED_SPEC.loader.exec_module(paired)

SCHEMA = "axeyum-glaurung-regime-features-v1"
TOKEN_RE = re.compile(
    r';[^\r\n]*|\|(?:\\.|[^|])*\||"(?:""|[^"])*"|[()]|[^\s()]+'
)
INTEGER_RE = re.compile(r"[0-9]+")
CONTINUOUS_FEATURES = (
    "query_bytes",
    "atom_count",
    "list_count",
    "max_sexpr_depth",
    "declaration_count",
    "assertion_count",
    "active_constraint_count",
    "query_occurrences_per_run",
    "operator_count",
    "boolean_operator_count",
    "ite_count",
    "bv_arithmetic_count",
    "bv_bitwise_count",
    "bv_compare_count",
    "bv_shift_count",
    "bv_slice_extend_count",
    "bit_width_mention_count",
    "max_bv_width",
)

BOOLEAN_OPERATORS = {"and", "or", "not", "xor", "=>", "=", "distinct"}
BV_ARITHMETIC = {
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvsdiv",
    "bvurem",
    "bvsrem",
    "bvsmod",
    "bvneg",
}
BV_BITWISE = {"bvand", "bvor", "bvxor", "bvnot", "bvnand", "bvnor", "bvxnor"}
BV_COMPARE = {
    "bvult",
    "bvule",
    "bvugt",
    "bvuge",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "bvcomp",
}
BV_SHIFT = {"bvshl", "bvlshr", "bvashr", "rotate_left", "rotate_right"}
BV_SLICE_EXTEND = {"concat", "extract", "zero_extend", "sign_extend", "repeat"}
ALL_OPERATORS = (
    BOOLEAN_OPERATORS
    | BV_ARITHMETIC
    | BV_BITWISE
    | BV_COMPARE
    | BV_SHIFT
    | BV_SLICE_EXTEND
    | {"ite", "select", "store"}
)


def fail(message: str) -> None:
    raise paired.AnalysisError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json_bytes(path: pathlib.Path) -> tuple[dict[str, Any], bytes]:
    try:
        data = path.read_bytes()
        value = json.loads(data)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        fail(f"cannot read {path}: {error}")
    if not isinstance(value, dict):
        fail(f"{path} is not a JSON object")
    return value, data


def geometric_mean(values: Sequence[float]) -> float:
    if not values or any(value <= 0 or not math.isfinite(value) for value in values):
        fail("geometric mean requires finite positive values")
    return math.exp(math.fsum(math.log(value) for value in values) / len(values))


def tokens_without_comments(text: str) -> list[str]:
    return [token for token in TOKEN_RE.findall(text) if not token.startswith(";")]


def query_features(data: bytes) -> dict[str, int]:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        fail(f"query is not UTF-8: {error}")
    tokens = tokens_without_comments(text)
    atoms = [token for token in tokens if token not in {"(", ")"}]
    counts = Counter(atoms)
    depth = 0
    max_depth = 0
    for token in tokens:
        if token == "(":
            depth += 1
            max_depth = max(max_depth, depth)
        elif token == ")":
            depth -= 1
            if depth < 0:
                fail("query has an unmatched closing parenthesis")
    if depth != 0:
        fail("query has unmatched opening parentheses")

    width_mentions: list[int] = []
    for index in range(len(tokens) - 3):
        if tokens[index : index + 3] == ["(", "_", "BitVec"]:
            width = tokens[index + 3]
            if INTEGER_RE.fullmatch(width):
                width_mentions.append(int(width))
        elif tokens[index : index + 2] == ["(", "_"]:
            constant = tokens[index + 2]
            width = tokens[index + 3]
            if constant.startswith("bv") and INTEGER_RE.fullmatch(width):
                width_mentions.append(int(width))

    return {
        "query_bytes": len(data),
        "atom_count": len(atoms),
        "list_count": tokens.count("("),
        "max_sexpr_depth": max_depth,
        "declaration_count": counts["declare-const"] + counts["declare-fun"],
        "assertion_count": counts["assert"],
        "operator_count": sum(counts[operator] for operator in ALL_OPERATORS),
        "boolean_operator_count": sum(
            counts[operator] for operator in BOOLEAN_OPERATORS
        ),
        "ite_count": counts["ite"],
        "bv_arithmetic_count": sum(counts[operator] for operator in BV_ARITHMETIC),
        "bv_bitwise_count": sum(counts[operator] for operator in BV_BITWISE),
        "bv_compare_count": sum(counts[operator] for operator in BV_COMPARE),
        "bv_shift_count": sum(counts[operator] for operator in BV_SHIFT),
        "bv_slice_extend_count": sum(
            counts[operator] for operator in BV_SLICE_EXTEND
        ),
        "bit_width_mention_count": len(width_mentions),
        "max_bv_width": max(width_mentions, default=0),
    }


def average_ranks(values: Sequence[float]) -> list[float]:
    ordered = sorted(enumerate(values), key=lambda item: item[1])
    ranks = [0.0] * len(values)
    start = 0
    while start < len(ordered):
        end = start + 1
        while end < len(ordered) and ordered[end][1] == ordered[start][1]:
            end += 1
        rank = (start + 1 + end) / 2.0
        for index in range(start, end):
            ranks[ordered[index][0]] = rank
        start = end
    return ranks


def pearson(left: Sequence[float], right: Sequence[float]) -> float | None:
    if len(left) != len(right) or len(left) < 2:
        return None
    left_mean = statistics.fmean(left)
    right_mean = statistics.fmean(right)
    left_delta = [value - left_mean for value in left]
    right_delta = [value - right_mean for value in right]
    denominator = math.sqrt(
        math.fsum(value * value for value in left_delta)
        * math.fsum(value * value for value in right_delta)
    )
    if denominator == 0:
        return None
    return math.fsum(a * b for a, b in zip(left_delta, right_delta)) / denominator


def spearman(left: Sequence[float], right: Sequence[float]) -> float | None:
    return pearson(average_ranks(left), average_ranks(right))


def nearest_rank(values: Sequence[float], quantile: float) -> float:
    if not values:
        fail("cannot take a quantile of an empty sample")
    ordered = sorted(values)
    return ordered[min(len(ordered) - 1, max(0, math.ceil(quantile * len(ordered)) - 1))]


def numeric_summary(values: Sequence[float]) -> dict[str, float]:
    return {
        "minimum": min(values),
        "p50": nearest_rank(values, 0.50),
        "p90": nearest_rank(values, 0.90),
        "maximum": max(values),
        "mean": statistics.fmean(values),
    }


def ratio_summary(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return {
        "occurrences": len(rows),
        "warm_z3_over_axeyum_geomean": geometric_mean(
            [row["warm_z3_over_axeyum"] for row in rows]
        ),
        "cold_z3_over_axeyum_geomean": geometric_mean(
            [row["cold_z3_over_axeyum"] for row in rows]
        ),
    }


def group_ratios(rows: Sequence[dict[str, Any]], key: str) -> dict[str, Any]:
    groups: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        groups.setdefault(str(row[key]), []).append(row)
    return {name: ratio_summary(group) for name, group in sorted(groups.items())}


def feature_summary(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    warm_logs = [math.log(row["warm_z3_over_axeyum"]) for row in rows]
    cold_logs = [math.log(row["cold_z3_over_axeyum"]) for row in rows]
    result: dict[str, Any] = {}
    for feature in CONTINUOUS_FEATURES:
        values = [float(row[feature]) for row in rows]
        result[feature] = {
            "distribution": numeric_summary(values),
            "spearman_vs_log_warm_ratio": spearman(values, warm_logs),
            "spearman_vs_log_cold_ratio": spearman(values, cold_logs),
        }
    return result


def quartile_summaries(
    rows: Sequence[dict[str, Any]], feature: str
) -> list[dict[str, Any]]:
    thresholds = [
        nearest_rank([float(row[feature]) for row in rows], quantile)
        for quantile in (0.25, 0.50, 0.75)
    ]
    groups: list[list[dict[str, Any]]] = [[], [], [], []]
    for row in rows:
        value = float(row[feature])
        group_index = sum(value > threshold for threshold in thresholds)
        groups[group_index].append(row)
    bins: list[dict[str, Any]] = []
    for quartile, group in enumerate(groups, 1):
        if not group:
            continue
        group.sort(key=lambda row: (row[feature], row["driver"], row["index"]))
        summary = ratio_summary(group)
        summary.update(
            {
                "quantile_bin": quartile,
                "feature_minimum": group[0][feature],
                "feature_maximum": group[-1][feature],
                "driver_counts": dict(
                    sorted(Counter(row["driver"] for row in group).items())
                ),
            }
        )
        bins.append(summary)
    return bins


def composition_standardized(
    rows: Sequence[dict[str, Any]], key: str
) -> dict[str, Any]:
    categories = sorted({str(row[key]) for row in rows})
    category_counts = Counter(str(row[key]) for row in rows)
    weights = {
        category: category_counts[category] / len(rows) for category in categories
    }
    by_driver: dict[str, Any] = {}
    for driver in sorted({row["driver"] for row in rows}):
        driver_rows = [row for row in rows if row["driver"] == driver]
        groups = {
            category: [row for row in driver_rows if str(row[key]) == category]
            for category in categories
        }
        if any(not group for group in groups.values()):
            by_driver[driver] = {
                "available": False,
                "missing_categories": [
                    category for category, group in groups.items() if not group
                ],
            }
            continue
        observed = ratio_summary(driver_rows)
        standardized: dict[str, float] = {}
        for cell in ("warm_z3_over_axeyum", "cold_z3_over_axeyum"):
            standardized[f"{cell}_geomean"] = math.exp(
                math.fsum(
                    weights[category]
                    * math.log(geometric_mean([row[cell] for row in group]))
                    for category, group in groups.items()
                )
            )
        by_driver[driver] = {
            "available": True,
            "observed": observed,
            "standardized_to_pooled_category_weights": standardized,
        }
    return {"pooled_weights": weights, "drivers": by_driver}


def validate_report(
    report_path: pathlib.Path,
) -> tuple[dict[str, Any], bytes, list[Any]]:
    report, report_bytes = load_json_bytes(report_path)
    if report.get("schema") != "axeyum-glaurung-paired-analysis-v1":
        fail(f"unsupported paired report schema in {report_path}")
    if report.get("input_measurement_schema") != paired.MEASUREMENT_SCHEMA_V2:
        fail(f"feature attribution requires four-cell v2 input: {report_path}")
    roots_value = report.get("trace_paths")
    if not isinstance(roots_value, list) or len(roots_value) < 5:
        fail(f"report has fewer than five trace paths: {report_path}")
    roots = [pathlib.Path(value) for value in roots_value]
    traces = [paired.load_trace(root) for root in roots]
    baseline = traces[0]
    identities = tuple(check.identity for check in baseline.checks)
    for trace in traces[1:]:
        if trace.driver_sha256 != baseline.driver_sha256:
            fail(f"driver drift in {trace.path}")
        if trace.configuration_identity != baseline.configuration_identity:
            fail(f"configuration drift in {trace.path}")
        if tuple(check.identity for check in trace.checks) != identities:
            fail(f"fixed-work identity drift in {trace.path}")
    if report.get("repetitions") != len(traces):
        fail(f"repetition count mismatch in {report_path}")
    if report.get("fixed_work_checks_per_repetition") != len(baseline.checks):
        fail(f"check count mismatch in {report_path}")
    driver = report.get("driver")
    if not isinstance(driver, dict) or driver.get("sha256") != baseline.driver_sha256:
        fail(f"driver identity mismatch in {report_path}")
    return report, report_bytes, traces


def rows_for_report(
    report_path: pathlib.Path,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    report, report_bytes, traces = validate_report(report_path)
    baseline = traces[0]
    query_counts = Counter(check.query_sha256 for check in baseline.checks)
    feature_cache: dict[str, dict[str, int]] = {}
    rows: list[dict[str, Any]] = []
    for index, check in enumerate(baseline.checks):
        cell_outcomes = [
            getattr(trace.checks[index], f"{cell}_outcome")
            for trace in traces
            for cell in ("z3_cold", "z3_warm", "axeyum_cold", "axeyum_warm")
        ]
        if any(outcome not in paired.DECIDED for outcome in cell_outcomes):
            fail(f"nondecided occurrence {check.check_id} in {report_path}")
        if len(set(cell_outcomes)) != 1:
            fail(f"outcome drift for {check.check_id} in {report_path}")
        if check.query_sha256 not in feature_cache:
            query_path = baseline.path / "queries" / f"{check.query_sha256}.smt2"
            try:
                query_bytes = query_path.read_bytes()
            except OSError as error:
                fail(f"cannot read {query_path}: {error}")
            if sha256(query_bytes) != check.query_sha256:
                fail(f"query hash mismatch for {query_path}")
            feature_cache[check.query_sha256] = query_features(query_bytes)
        warm_ratios = [
            int(trace.checks[index].z3_warm_nanos)
            / int(trace.checks[index].axeyum_warm_nanos)
            for trace in traces
        ]
        cold_ratios = [
            int(trace.checks[index].z3_cold_nanos)
            / int(trace.checks[index].axeyum_cold_nanos)
            for trace in traces
        ]
        row: dict[str, Any] = {
            "driver": baseline.driver_label,
            "driver_sha256": baseline.driver_sha256,
            "index": index,
            "check_id": check.check_id,
            "query_sha256": check.query_sha256,
            "purpose": check.purpose,
            "outcome": cell_outcomes[0],
            "warm_execution": check.axeyum_warm_execution,
            "active_constraint_count": check.active_constraint_count,
            "query_occurrences_per_run": query_counts[check.query_sha256],
            "warm_z3_over_axeyum": geometric_mean(warm_ratios),
            "cold_z3_over_axeyum": geometric_mean(cold_ratios),
        }
        row.update(feature_cache[check.query_sha256])
        rows.append(row)

    expected = report["four_cell_comparisons"]
    actual = ratio_summary(rows)
    comparisons = (
        (actual["warm_z3_over_axeyum_geomean"], expected["warm_z3_over_axeyum"]),
        (actual["cold_z3_over_axeyum_geomean"], expected["cold_z3_over_axeyum"]),
    )
    for value, expected_group in comparisons:
        if not math.isclose(
            value,
            expected_group["per_occurrence_geomean_speedup"],
            rel_tol=1e-12,
        ):
            fail(f"paired ratio mismatch in {report_path}")
    provenance = {
        "path": str(report_path),
        "sha256": sha256(report_bytes),
        "driver": report["driver"],
        "repetitions": report["repetitions"],
        "occurrences": len(rows),
    }
    return provenance, rows


def analyze(report_paths: Sequence[pathlib.Path]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if len(report_paths) < 2:
        fail("regime attribution requires at least two driver reports")
    provenance: list[dict[str, Any]] = []
    all_rows: list[dict[str, Any]] = []
    seen_drivers: set[str] = set()
    for path in report_paths:
        source, rows = rows_for_report(path)
        driver_sha256 = source["driver"]["sha256"]
        if driver_sha256 in seen_drivers:
            fail(f"duplicate driver report: {path}")
        seen_drivers.add(driver_sha256)
        provenance.append(source)
        all_rows.extend(rows)

    by_driver: dict[str, Any] = {}
    for driver in sorted({row["driver"] for row in all_rows}):
        rows = [row for row in all_rows if row["driver"] == driver]
        by_driver[driver] = {
            **ratio_summary(rows),
            "features": feature_summary(rows),
            "by_outcome": group_ratios(rows, "outcome"),
            "by_purpose": group_ratios(rows, "purpose"),
            "by_warm_execution": group_ratios(rows, "warm_execution"),
        }
    report = {
        "schema": SCHEMA,
        "input_reports": provenance,
        "methodology": {
            "unit": "stable ordered check occurrence",
            "ratio": "paired per-occurrence geometric mean across repetitions",
            "ratio_direction": "z3_nanos/axeyum_nanos; greater than 1 favors Axeyum",
            "query_features": "lexical features of hash-verified canonical SMT-LIB",
            "correlation": "Spearman rank correlation against log paired ratio",
            "interpretation": "descriptive attribution only; driver and query features are observational",
        },
        "occurrences": len(all_rows),
        "drivers": by_driver,
        "pooled_descriptive_features": feature_summary(all_rows),
        "pooled_feature_quartiles": {
            feature: quartile_summaries(all_rows, feature)
            for feature in CONTINUOUS_FEATURES
        },
        "composition_controls": {
            "outcome": composition_standardized(all_rows, "outcome"),
            "purpose": composition_standardized(all_rows, "purpose"),
        },
    }
    return report, all_rows


def write_csv(rows: Iterable[dict[str, Any]], path: pathlib.Path) -> None:
    rows = list(rows)
    if not rows:
        fail("cannot write an empty feature table")
    fieldnames = list(rows[0])
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reports", nargs="+", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--rows-csv", type=pathlib.Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        report, rows = analyze(args.reports)
        if args.rows_csv is not None:
            write_csv(rows, args.rows_csv)
        rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output is None:
            sys.stdout.write(rendered)
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")
    except paired.AnalysisError as error:
        print(f"regime feature analysis failed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
