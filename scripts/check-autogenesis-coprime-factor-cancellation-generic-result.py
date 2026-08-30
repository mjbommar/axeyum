#!/usr/bin/env python3
"""Verify the fail-closed first generic cancellation result."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/coprime-factor-cancellation-generic-result-v1.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    result = json.loads(RESULT.read_text())
    require(result["state"] == "compilation-declined-missing-bound-support-module-no-retry", "state changed")
    require(digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"], "plan changed")
    require(digest(ROOT / result["source"]["path"]) == result["source"]["sha256"], "source changed")
    pack = Path(result["evidence"]["pack"])
    require(digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"], "manifest changed")
    require(digest(pack / "compile.stdout") == result["evidence"]["compile_stdout_sha256"], "diagnostic changed")
    diagnostic = (pack / "compile.stdout").read_text()
    require("unknown module prefix 'AxeyumAutogenesisBalancedBezoutEuclideanUpdateV2'" in diagnostic, "expected module decline absent")
    require((pack / "compile.stderr").read_bytes() == b"", "unexpected stderr")
    require(result["execution"] == {"source_copies": 1, "compiler_invocations": 1, "successful_compilations": 0, "exporter_invocations": 0, "importer_runs": 0, "proof_bearing_stream_reads": 0, "retries": 0}, "execution changed")
    require(result["decline"] == {"stage": "module-resolution-before-elaboration", "missing_module": "AxeyumAutogenesisBalancedBezoutEuclideanUpdateV2", "theorem_submissions": 0, "proof_material_rendered": False}, "decline changed")
    require(result["cleanup"] == {"exact_temporary_paths_removed": 1, "preexisting_baseline_unchanged": True}, "cleanup changed")
    require(all(value == 0 for value in result["authority"].values()), "decline grants authority")
    print("AUTOGENESIS_COPRIME_FACTOR_CANCELLATION_GENERIC_RESULT_OK|compile=declined|exports=0|imports=0|authority=0")


if __name__ == "__main__":
    main()
