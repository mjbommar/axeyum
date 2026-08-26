#!/usr/bin/env python3
"""Replay a hash-pinned external certificate checker and emit a bounded receipt.

This is an import boundary, not an Axeyum proof checker.  A successful receipt
means that the exact named third-party executable accepted the exact named
artifacts under the recorded wall-clock policy.  It grants no fact-ledger or
kernel authority by itself.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import NoReturn


SCHEMA = "axeyum.external-certificate-check.v1"
RECEIPT_SCHEMA = "axeyum.external-certificate-receipt.v1"
MAX_TIMEOUT_SECONDS = 86_400
MAX_CAPTURE_BYTES = 16 * 1024 * 1024


class ManifestError(ValueError):
    """The manifest is malformed or does not match the files on disk."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def require_sha256(value: object, field: str) -> str:
    if not isinstance(value, str) or len(value) != 64:
        raise ManifestError(f"{field} must be a lowercase SHA-256 digest")
    if any(character not in "0123456789abcdef" for character in value):
        raise ManifestError(f"{field} must be a lowercase SHA-256 digest")
    return value


def resolve_file(base: Path, value: object, field: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ManifestError(f"{field} must be a nonempty path")
    path = Path(value)
    if not path.is_absolute():
        path = base / path
    path = path.resolve(strict=True)
    if not path.is_file():
        raise ManifestError(f"{field} is not a regular file: {path}")
    return path


def checked_file(base: Path, entry: object, field: str) -> tuple[Path, str]:
    if not isinstance(entry, dict):
        raise ManifestError(f"{field} must be an object")
    path = resolve_file(base, entry.get("path"), f"{field}.path")
    expected = require_sha256(entry.get("sha256"), f"{field}.sha256")
    observed = sha256_file(path)
    if observed != expected:
        raise ManifestError(
            f"{field} digest mismatch: expected {expected}, observed {observed}"
        )
    return path, observed


def canonical_digest(value: object) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def output_observation(path: Path, limit: int) -> dict[str, object]:
    size = path.stat().st_size
    digest = sha256_file(path)
    with path.open("rb") as stream:
        if size > limit:
            stream.seek(size - limit)
        tail = stream.read().decode("utf-8", errors="replace")
    return {
        "bytes": size,
        "sha256": digest,
        "tail": tail,
        "tail_truncated": size > limit,
    }


def fail(message: str, exit_code: int = 2) -> NoReturn:
    print(f"external-certificate-check: {message}", file=sys.stderr)
    raise SystemExit(exit_code)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    try:
        manifest_path = args.manifest.resolve(strict=True)
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if not isinstance(manifest, dict) or manifest.get("schema") != SCHEMA:
            raise ManifestError(f"schema must be {SCHEMA!r}")
        base = manifest_path.parent
        checker_path, checker_digest = checked_file(base, manifest.get("checker"), "checker")

        artifact_entries = manifest.get("artifacts")
        if not isinstance(artifact_entries, list) or not artifact_entries:
            raise ManifestError("artifacts must be a nonempty array")
        artifacts: dict[str, tuple[Path, str]] = {}
        artifact_receipts = []
        for index, entry in enumerate(artifact_entries):
            if not isinstance(entry, dict):
                raise ManifestError(f"artifacts[{index}] must be an object")
            role = entry.get("role")
            if not isinstance(role, str) or not role or role in artifacts:
                raise ManifestError(f"artifacts[{index}].role must be unique and nonempty")
            path, digest = checked_file(base, entry, f"artifacts[{index}]")
            artifacts[role] = (path, digest)
            artifact_receipts.append(
                {"role": role, "path": str(path), "sha256": digest, "bytes": path.stat().st_size}
            )

        raw_argv = manifest.get("argv")
        if not isinstance(raw_argv, list) or not all(isinstance(arg, str) for arg in raw_argv):
            raise ManifestError("argv must be an array of strings")
        command = [str(checker_path)]
        for index, argument in enumerate(raw_argv):
            if argument.startswith("{artifact:") and argument.endswith("}"):
                role = argument[len("{artifact:") : -1]
                if role not in artifacts:
                    raise ManifestError(f"argv[{index}] names unknown artifact role {role!r}")
                command.append(str(artifacts[role][0]))
            elif "{artifact:" in argument:
                raise ManifestError(
                    f"argv[{index}] must use an artifact placeholder as the whole argument"
                )
            else:
                command.append(argument)

        timeout = manifest.get("timeout_seconds")
        if not isinstance(timeout, int) or isinstance(timeout, bool) or not 1 <= timeout <= MAX_TIMEOUT_SECONDS:
            raise ManifestError(f"timeout_seconds must be in 1..={MAX_TIMEOUT_SECONDS}")
        success = manifest.get("success")
        if not isinstance(success, dict):
            raise ManifestError("success must be an object")
        exit_codes = success.get("exit_codes")
        if (
            not isinstance(exit_codes, list)
            or not exit_codes
            or not all(isinstance(code, int) and not isinstance(code, bool) for code in exit_codes)
        ):
            raise ManifestError("success.exit_codes must be a nonempty integer array")
        required_stdout = success.get("stdout_contains", [])
        required_stderr = success.get("stderr_contains", [])
        if not isinstance(required_stdout, list) or not all(isinstance(item, str) for item in required_stdout):
            raise ManifestError("success.stdout_contains must be an array of strings")
        if not isinstance(required_stderr, list) or not all(isinstance(item, str) for item in required_stderr):
            raise ManifestError("success.stderr_contains must be an array of strings")
        if not required_stdout and not required_stderr:
            raise ManifestError("success must require at least one output substring")
    except (OSError, json.JSONDecodeError, ManifestError) as error:
        fail(str(error))

    started = time.monotonic()
    timed_out = False
    with tempfile.TemporaryDirectory(prefix="axeyum-external-check-") as temporary:
        stdout_path = Path(temporary) / "stdout"
        stderr_path = Path(temporary) / "stderr"
        with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
            process = subprocess.Popen(
                command,
                cwd=base,
                stdin=subprocess.DEVNULL,
                stdout=stdout,
                stderr=stderr,
                start_new_session=True,
            )
            try:
                exit_code = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                exit_code = process.wait()
        elapsed_ms = round((time.monotonic() - started) * 1000)
        stdout_observation = output_observation(stdout_path, MAX_CAPTURE_BYTES)
        stderr_observation = output_observation(stderr_path, MAX_CAPTURE_BYTES)

    stdout_text = str(stdout_observation["tail"])
    stderr_text = str(stderr_observation["tail"])
    output_complete = not stdout_observation["tail_truncated"] and not stderr_observation["tail_truncated"]
    output_matches = output_complete and all(item in stdout_text for item in required_stdout) and all(
        item in stderr_text for item in required_stderr
    )
    verified = not timed_out and exit_code in exit_codes and output_matches
    receipt = {
        "schema": RECEIPT_SCHEMA,
        "manifest_sha256": canonical_digest(manifest),
        "checker": {
            "path": str(checker_path),
            "sha256": checker_digest,
            "bytes": checker_path.stat().st_size,
        },
        "artifacts": artifact_receipts,
        "policy": {"timeout_seconds": timeout, "output_capture_limit_bytes": MAX_CAPTURE_BYTES},
        "observation": {
            "verdict": "verified" if verified else ("timeout" if timed_out else "failed"),
            "exit_code": exit_code,
            "elapsed_ms": elapsed_ms,
            "stdout": stdout_observation,
            "stderr": stderr_observation,
        },
    }
    receipt["receipt_sha256"] = canonical_digest(receipt)
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0 if verified else (3 if timed_out else 1)


if __name__ == "__main__":
    raise SystemExit(main())
