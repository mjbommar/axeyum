#!/usr/bin/env python3
"""Run the pinned organizer cache builder and sampler inside one fresh venv."""

from __future__ import annotations

import argparse
import ast
import hashlib
import itertools
import json
import platform
import sys
from pathlib import Path
from typing import Any, Dict


EXPECTED_CACHE_AST_SHA256 = "ca792a127fb4f5d0c40bd5055b370a3cfb27bb28bdf2c5d4724d5e69d2009617"


def canonical_json_bytes(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, separators=(",", ":"), sort_keys=True) + "\n").encode()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while data := source.read(1024 * 1024):
            digest.update(data)
    return digest.hexdigest()


def load_official_cache_builder(bundle: Path, namespace: dict[str, object]) -> tuple[object, str]:
    source_path = bundle / "smtcomp/main.py"
    source = source_path.read_bytes()
    tree = ast.parse(source, filename=str(source_path))
    matches = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "create_cache"]
    if len(matches) != 1:
        raise RuntimeError("pinned main.py does not contain exactly one create_cache function")
    function = matches[0]
    function.decorator_list = []
    module = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
    exec(compile(module, str(source_path), "exec"), namespace)
    return namespace["create_cache"], hashlib.sha256(ast.dump(function, include_attributes=False).encode()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    bundle = args.bundle.resolve(strict=True)
    output = args.output
    if output.exists():
        raise RuntimeError(f"worker output already exists: {output}")
    output.mkdir(parents=True)

    sys.path.insert(0, str(bundle))
    import polars as pl
    from rich.progress import track
    from smtcomp import defs, selection
    from smtcomp.unpack import read_cin

    if pl.__version__ != "1.39.2":
        raise RuntimeError(f"wrong Polars version: {pl.__version__}")
    data = bundle / "data"
    namespace: dict[str, object] = {
        "Any": Any,
        "Dict": Dict,
        "Path": Path,
        "defs": defs,
        "itertools": itertools,
        "pl": pl,
        "read_cin": read_cin,
        "track": track,
    }
    cache_builder, cache_ast_sha256 = load_official_cache_builder(bundle, namespace)
    if cache_ast_sha256 != EXPECTED_CACHE_AST_SHA256:
        raise RuntimeError(f"wrong official create_cache AST identity: {cache_ast_sha256}")
    cache_builder(data)

    config = defs.Config(data)
    if config.seed != 22_731_074:
        raise RuntimeError(f"wrong official seed: {config.seed}")
    benchmarks = defs.Benchmarks.model_validate_json(read_cin(config.benchmarks))
    if len(benchmarks.non_incremental) != 450_472:
        raise RuntimeError(f"wrong non-incremental population: {len(benchmarks.non_incremental)}")
    selected = (
        selection.helper(config, defs.Track.SingleQuery)
        .filter(pl.col("selected"))
        .select("file", "logic", "new")
        .collect()
    )
    rows = selected.to_dicts()
    paths: list[str] = []
    per_logic: dict[str, dict[str, int | str]] = {}
    seen_ids: set[int] = set()
    for row in rows:
        file_id = row["file"]
        if isinstance(file_id, bool) or not isinstance(file_id, int) or not 0 <= file_id < 450_472:
            raise RuntimeError(f"invalid selected file ID: {file_id!r}")
        if file_id in seen_ids:
            raise RuntimeError(f"duplicate selected file ID: {file_id}")
        seen_ids.add(file_id)
        benchmark = benchmarks.non_incremental[file_id].file
        logic = str(benchmark.logic)
        if int(benchmark.logic) != row["logic"]:
            raise RuntimeError(f"selected logic/file mismatch: {file_id}")
        paths.append(benchmark.path().as_posix())
        counts = per_logic.setdefault(logic, {"logic": logic, "new": 0, "old": 0, "selected": 0})
        category = "new" if row["new"] is True else "old"
        counts[category] = int(counts[category]) + 1
        counts["selected"] = int(counts["selected"]) + 1
    paths.sort()
    if len(paths) != len(set(paths)):
        raise RuntimeError("selected paths are not unique")
    selected_bytes = ("\n".join(paths) + "\n").encode()
    (output / "official-selected.txt").write_bytes(selected_bytes)
    per_logic_document = {
        "logics": [per_logic[name] for name in sorted(per_logic)],
        "schema": "axeyum-smtcomp-official-producer-per-logic-v1",
        "selected": len(paths),
    }
    (output / "per-logic.json").write_bytes(canonical_json_bytes(per_logic_document))

    cache_paths = [
        config.cached_non_incremental_benchmarks,
        config.cached_incremental_benchmarks,
        config.cached_previous_results,
    ]
    worker = {
        "cache_builder_ast_sha256": cache_ast_sha256,
        "caches": [
            {"bytes": path.stat().st_size, "name": path.name, "sha256": sha256_file(path)}
            for path in cache_paths
        ],
        "implementation": platform.python_implementation(),
        "per_logic_sha256": sha256_file(output / "per-logic.json"),
        "polars": pl.__version__,
        "python": platform.python_version(),
        "schema": "axeyum-smtcomp-official-producer-worker-v1",
        "seed": config.seed,
        "selected": len(paths),
        "selected_sha256": hashlib.sha256(selected_bytes).hexdigest(),
        "thread_pool_size": pl.thread_pool_size(),
    }
    (output / "worker.json").write_bytes(canonical_json_bytes(worker))
    print(f"SMTCOMP_OFFICIAL_PRODUCER_WORKER|selected={len(paths)}|polars={pl.__version__}|seed={config.seed}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
