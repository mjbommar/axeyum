#!/usr/bin/env python3
"""Diagnose ADR-0323's two-root Maestro LLVM drift without granting credit."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Sequence


REPO = Path(__file__).resolve().parents[1]
CAPTURE_SCRIPT = Path(__file__).with_name("capture-maestro-device-id.py")
CAPTURE_SPEC = importlib.util.spec_from_file_location("maestro_capture", CAPTURE_SCRIPT)
if CAPTURE_SPEC is None or CAPTURE_SPEC.loader is None:
    raise RuntimeError(f"cannot load capture support from {CAPTURE_SCRIPT}")
CAPTURE = importlib.util.module_from_spec(CAPTURE_SPEC)
sys.modules[CAPTURE_SPEC.name] = CAPTURE
CAPTURE_SPEC.loader.exec_module(CAPTURE)

DEFAULT_REGISTRATION = (
    REPO / "bench-results/verify-maestro-device-id-20260721/drift-registration.json"
)
DEFAULT_OUTPUT = REPO / "target/maestro-device-id-20260721/drift-diagnostic"
RESULT_SCHEMA = "axeyum.maestro-llvm-root-drift-result.v1"
HUNK = re.compile(rb"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")
SYMBOL_SHAPES = {
    "major": re.compile(rb"_ZN6kernel6device2id5major17h[0-9a-f]{16}E"),
    "minor": re.compile(rb"_ZN6kernel6device2id5minor17h[0-9a-f]{16}E"),
    "makedev": re.compile(rb"_ZN6kernel6device2id7makedev17h[0-9a-f]{16}E"),
}


def validate_registration(registration: dict[str, Any]) -> None:
    CAPTURE.require(
        registration.get("schema") == "axeyum.maestro-llvm-root-drift-registration.v1",
        "registration", "schema", "diagnostic registration schema drift",
    )
    for field in ("capture_registration", "capture_result"):
        entry = registration.get(field)
        CAPTURE.require(isinstance(entry, dict), "registration", "shape", field)
        path = Path(CAPTURE.require_string(entry.get("path"), f"{field}.path"))
        digest = CAPTURE.require_string(entry.get("sha256"), f"{field}.sha256")
        CAPTURE.require(not path.is_absolute() and ".." not in path.parts,
                        "registration", "unsafe_path", str(path))
        CAPTURE.require(bool(CAPTURE.SHA256.fullmatch(digest)),
                        "registration", "shape", f"{field} hash")
    diff = registration.get("diff")
    CAPTURE.require(isinstance(diff, dict), "registration", "shape", "diff")
    CAPTURE.require(Path(CAPTURE.require_string(diff.get("path"), "diff.path")).is_absolute(),
                    "registration", "shape", "diff path")
    CAPTURE.require(bool(CAPTURE.SHA256.fullmatch(
        CAPTURE.require_string(diff.get("sha256"), "diff.sha256"))),
        "registration", "shape", "diff hash")
    CAPTURE.require(diff.get("version") == "diff (GNU diffutils) 3.12",
                    "registration", "version", "diff version")
    CAPTURE.validate_registration({
        **CAPTURE.read_json(REPO / registration["capture_registration"]["path"])
    })
    producers = registration.get("producer_files")
    CAPTURE.require(isinstance(producers, list) and producers,
                    "registration", "shape", "producer files")
    paths = [entry.get("path") for entry in producers if isinstance(entry, dict)]
    CAPTURE.require(paths == sorted(set(paths)), "registration", "ordering", "producer files")
    for entry in producers:
        path = REPO / CAPTURE.require_string(entry.get("path"), "producer.path")
        digest = CAPTURE.require_string(entry.get("sha256"), "producer.sha256")
        CAPTURE.require(path.is_file(), "registration", "missing_producer", str(path))
        CAPTURE.require(CAPTURE.sha256_file(path) == digest,
                        "registration", "producer_hash", str(path))


def validate_registered_inputs(registration: dict[str, Any]) -> dict[str, Any]:
    for field in ("capture_registration", "capture_result"):
        entry = registration[field]
        path = REPO / entry["path"]
        CAPTURE.require(path.is_file(), "registration", "missing_input", str(path))
        CAPTURE.require(CAPTURE.sha256_file(path) == entry["sha256"],
                        "registration", "input_hash", str(path))
    capture = CAPTURE.read_json(REPO / registration["capture_registration"]["path"])
    CAPTURE.validate_registration(capture)
    CAPTURE.validate_producers(capture)
    return capture


def classify_changed_line(line: bytes) -> str:
    stripped = line.strip()
    if stripped.startswith(b"; ModuleID =") or stripped.startswith(b"source_filename ="):
        return "module_source_identity"
    if stripped.startswith(b"target ") or stripped.startswith(b"module asm"):
        return "target_module_assembly"
    if stripped.startswith(b"attributes #"):
        return "attribute"
    if stripped.startswith(b"!") or b", !" in line:
        return "metadata"
    if (
        stripped.startswith((b"define ", b"declare ", b"@", b"$"))
        or b" comdat" in stripped
    ):
        return "global_function_comdat_identity"
    if line.startswith((b" ", b"\t")) or stripped == b"}" or stripped.endswith(b":"):
        return "function_body_or_terminator"
    if not stripped or stripped.startswith(b";"):
        return "comment_or_whitespace"
    return "other"


def analyze_diff(path: Path, roots: Sequence[Path]) -> dict[str, Any]:
    counts: Counter[str] = Counter()
    samples: dict[str, list[str]] = defaultdict(list)
    hunks = 0
    added = 0
    removed = 0
    old_lines: list[int] = []
    new_lines: list[int] = []
    root_tokens = [str(root).encode() for root in roots]
    root_occurrences = [0 for _ in roots]
    with path.open("rb") as source:
        for raw in source:
            match = HUNK.match(raw)
            if match:
                hunks += 1
                old_lines.append(int(match.group(1)))
                new_lines.append(int(match.group(3)))
                continue
            if raw.startswith((b"--- ", b"+++ ")):
                continue
            if raw.startswith(b"+") or raw.startswith(b"-"):
                sign = raw[:1]
                line = raw[1:]
                if sign == b"+":
                    added += 1
                else:
                    removed += 1
                bucket = classify_changed_line(line)
                counts[bucket] += 1
                digest = CAPTURE.sha256_bytes(line)
                if len(samples[bucket]) < 3:
                    samples[bucket].append(digest)
                for index, token in enumerate(root_tokens):
                    root_occurrences[index] += line.count(token)
    return {
        "bytes": path.stat().st_size,
        "sha256": CAPTURE.sha256_file(path),
        "hunks": hunks,
        "added_lines": added,
        "removed_lines": removed,
        "old_first_hunk_line": min(old_lines) if old_lines else None,
        "old_last_hunk_line": max(old_lines) if old_lines else None,
        "new_first_hunk_line": min(new_lines) if new_lines else None,
        "new_last_hunk_line": max(new_lines) if new_lines else None,
        "bucket_counts": dict(sorted(counts.items())),
        "sample_line_sha256": dict(sorted(samples.items())),
        "root_path_occurrences": root_occurrences,
        "classified_lines": sum(counts.values()),
    }


def run_diff(diff: Path, left: Path, right: Path, output: Path) -> int:
    argv = [
        "systemd-run", "--user", "--scope", "--quiet",
        "-p", "MemoryHigh=2500M", "-p", "MemoryMax=4G", "-p", "MemorySwapMax=512M",
        "choom", "-n", "200", "--", str(diff), "--speed-large-files", "--unified=0",
        str(left), str(right),
    ]
    with output.open("wb") as sink:
        completed = subprocess.run(argv, check=False, stdout=sink, stderr=subprocess.PIPE)
    CAPTURE.require(completed.returncode in (0, 1), "diff", "command",
                    completed.stderr.decode(errors="replace"))
    return completed.returncode


def discover_symbols(module: bytes) -> dict[str, str]:
    found: dict[str, str] = {}
    for name, pattern in SYMBOL_SHAPES.items():
        matches = sorted(set(match.group().decode() for match in pattern.finditer(module)))
        definitions = [
            symbol for symbol in matches if CAPTURE.definition_count(module, symbol) == 1
        ]
        CAPTURE.require(len(definitions) == 1, "symbols", "discovery",
                        f"{name}: matches={matches} definitions={definitions}")
        comment = f"; kernel::device::id::{name}".encode()
        CAPTURE.require(module.count(comment) == 1, "symbols", "demangled_comment", name)
        found[name] = definitions[0]
    return found


def selected_projection(
    module: Path,
    label: str,
    target: dict[str, Any],
    symbol: str,
    output: Path,
    llvm_extract: Path,
    llvm_as: Path,
    admitter: Path,
) -> dict[str, Any]:
    extracted = output / label / f"{target['name']}.ll"
    extracted.parent.mkdir(parents=True, exist_ok=True)
    CAPTURE.command(
        [str(llvm_extract), f"--func={symbol}", "-S", str(module), "-o", str(extracted)],
        stage="extract", kind="llvm_extract",
    )
    CAPTURE.assemble(llvm_as, extracted)
    raw = extracted.read_bytes()
    agnostic = CAPTURE.moduleid_agnostic(raw)
    canonical = output / label / f"{target['name']}.canonical.ll"
    admission = CAPTURE.parse_admission(
        CAPTURE.command(
            [str(admitter), str(extracted), str(canonical)],
            stage="admission", kind="classifier",
        ).stdout
    )
    CAPTURE.assemble(llvm_as, canonical)
    expected_widths = ",".join(str(width) for width in target["parameter_widths"])
    CAPTURE.require(admission["function"] == symbol, "admission", "function", symbol)
    CAPTURE.require(admission["parameter_widths"] == expected_widths,
                    "admission", "parameter_widths", target["name"])
    CAPTURE.require(int(admission["return_width"]) == target["return_width"],
                    "admission", "return_width", target["name"])
    return {
        "root": label,
        "symbol": symbol,
        "raw_bytes": len(raw),
        "raw_sha256": CAPTURE.sha256_bytes(raw),
        "moduleid_agnostic_sha256": CAPTURE.sha256_bytes(agnostic),
        "frontend_canonical_bytes": canonical.stat().st_size,
        "frontend_canonical_sha256": CAPTURE.sha256_file(canonical),
        "admission": admission,
    }


def run_diagnostic(args: argparse.Namespace) -> dict[str, Any]:
    registration_path = args.registration.resolve()
    registration = CAPTURE.read_json(registration_path)
    validate_registration(registration)
    capture = validate_registered_inputs(registration)
    CAPTURE.validate_source(args.maestro_repo.resolve(), capture)

    output = args.output.resolve()
    target_root = (REPO / "target").resolve()
    CAPTURE.require(output.is_relative_to(target_root), "output", "unsafe_path", str(output))
    CAPTURE.require(not output.exists(), "output", "exists", str(output))
    output.parent.mkdir(parents=True, exist_ok=True)
    partial = output.with_name(f".{output.name}.partial-{os.getpid()}")
    CAPTURE.require(not partial.exists(), "output", "partial_exists", str(partial))
    partial.mkdir()

    diff_path = Path(registration["diff"]["path"])
    CAPTURE.validate_tool(diff_path, registration["diff"]["sha256"], "diff")
    llvm_as = Path(capture["tools"]["llvm_as"]["path"])
    llvm_extract = Path(capture["tools"]["llvm_extract"]["path"])
    CAPTURE.validate_tool(llvm_as, capture["tools"]["llvm_as"]["sha256"], "llvm_as")
    CAPTURE.validate_tool(
        llvm_extract, capture["tools"]["llvm_extract"]["sha256"], "llvm_extract"
    )
    admitter = args.admitter.resolve()
    CAPTURE.require(admitter.is_file(), "admission", "missing_binary", str(admitter))

    try:
        with tempfile.TemporaryDirectory(prefix="maestro-drift-") as raw_temp:
            temp = Path(raw_temp)
            roots = [temp / "root-a", temp / "root-b"]
            for root in roots:
                CAPTURE.materialize(args.maestro_repo.resolve(), capture["upstream"]["commit"], root)
            if args.prepare_cache:
                CAPTURE.prepare_cache(roots[0], capture)

            modules: list[Path] = []
            builds: list[dict[str, Any]] = []
            for label, root in zip(("a", "b"), roots):
                module, observation = CAPTURE.build_module(
                    root, temp / f"cargo-{label}", capture
                )
                retained = partial / "modules" / f"kernel-{label}.ll"
                retained.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(module, retained)
                CAPTURE.assemble(llvm_as, retained)
                modules.append(retained)
                data = retained.read_bytes()
                builds.append(
                    {
                        "root": label,
                        "module_bytes": len(data),
                        "module_sha256": CAPTURE.sha256_bytes(data),
                        "module_lines": len(data.splitlines()),
                        "absolute_root_occurrences": data.count(str(root).encode()),
                        **observation,
                    }
                )

            complete_diff = partial / "complete.diff"
            diff_status = run_diff(diff_path, modules[0], modules[1], complete_diff)
            diff_report = analyze_diff(complete_diff, roots)
            CAPTURE.require(
                diff_report["classified_lines"]
                == diff_report["added_lines"] + diff_report["removed_lines"],
                "diff", "line_loss", str(diff_report),
            )

            module_data = [module.read_bytes() for module in modules]
            discovered = [discover_symbols(data) for data in module_data]
            selected: list[dict[str, Any]] = []
            for target in capture["targets"]:
                rows = [
                    selected_projection(
                        module, label, target, symbols[target["name"]], partial / "selected",
                        llvm_extract, llvm_as, admitter,
                    )
                    for module, label, symbols in zip(modules, ("a", "b"), discovered)
                ]
                selected.append(
                    {
                        "name": target["name"],
                        "symbol_equal": rows[0]["symbol"] == rows[1]["symbol"],
                        "moduleid_agnostic_equal": rows[0]["moduleid_agnostic_sha256"]
                        == rows[1]["moduleid_agnostic_sha256"],
                        "frontend_canonical_equal": rows[0]["frontend_canonical_sha256"]
                        == rows[1]["frontend_canonical_sha256"],
                        "roots": rows,
                    }
                )

        status = "no_drift_reproduced" if diff_status == 0 else "drift_classified"
        result: dict[str, Any] = {
            "schema": RESULT_SCHEMA,
            "status": status,
            "capture_credit": False,
            "registration_sha256": CAPTURE.sha256_file(registration_path),
            "upstream": capture["upstream"],
            "builds": builds,
            "diff": diff_report,
            "selected": selected,
            "summary": {
                "builds": 2,
                "targets": 3,
                "dropped": 0,
                "solver_queries": 0,
                "all_selected_symbols_equal": all(row["symbol_equal"] for row in selected),
                "all_selected_moduleid_agnostic_equal": all(
                    row["moduleid_agnostic_equal"] for row in selected
                ),
                "all_selected_frontend_canonical_equal": all(
                    row["frontend_canonical_equal"] for row in selected
                ),
            },
        }
        result["identity_sha256"] = CAPTURE.sha256_bytes(
            (json.dumps({k: v for k, v in result.items() if k != "identity_sha256"},
                        sort_keys=True, separators=(",", ":")) + "\n").encode()
        )
        (partial / "drift-result.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        partial.rename(output)
        return result
    except BaseException:
        shutil.rmtree(partial, ignore_errors=True)
        raise


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registration", type=Path, default=DEFAULT_REGISTRATION)
    parser.add_argument("--maestro-repo", type=Path, default=CAPTURE.DEFAULT_MAESTRO)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--admitter", type=Path, default=CAPTURE.DEFAULT_ADMITTER)
    parser.add_argument("--prepare-cache", action="store_true")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        result = run_diagnostic(args)
    except CAPTURE.CaptureError as error:
        print(f"stage={error.stage}", file=sys.stderr)
        print(f"kind={error.kind}", file=sys.stderr)
        print(f"detail={error.detail}", file=sys.stderr)
        return 1
    print(f"status={result['status']}")
    print(f"identity_sha256={result['identity_sha256']}")
    print(f"output={args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
