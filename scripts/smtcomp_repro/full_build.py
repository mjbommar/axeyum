"""Exact-source Axeyum build authority for credited full preparation.

The live path owns one locked, offline release build before a shared attempt is
created.  The resulting bytes and byte-exact output are carried in memory until
they can be installed beneath the append-only preparation root.  Durable replay
uses the retained observation and products; it never pretends mutable compiler
installations were copied into the preparation.
"""

from __future__ import annotations

import copy
import hashlib
import os
import pwd
import shutil
import subprocess
import tempfile
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from full_readiness import require_exact_integrated_main
from resume_contract import ContractError, digest
from resume_fs import atomic_install_bytes, atomic_install_json
from resume_runner import sha256_file


BUILD_SCHEMA = "axeyum.smtcomp-credited-full-axeyum-build.v1"
BUILD_COMMAND = (
    "cargo",
    "build",
    "--release",
    "--locked",
    "--offline",
    "-p",
    "axeyum-bench",
    "--example",
    "smtcomp_cli",
)
BUILD_FIXED_ENVIRONMENT = {
    "CARGO_BUILD_JOBS": "2",
    "CARGO_TERM_COLOR": "never",
    "LANG": "C.UTF-8",
    "LC_ALL": "C.UTF-8",
    "NO_COLOR": "1",
    "PYTHONHASHSEED": "0",
    "PYTHONNOUSERSITE": "1",
    "PYTHONWARNINGS": "error",
    "TZ": "UTC",
}
BUILD_ACCOUNT_KEYS = {
    "CARGO_HOME",
    "HOME",
    "LOGNAME",
    "PATH",
    "RUSTUP_HOME",
    "USER",
}
BUILD_DYNAMIC_KEYS = {"CARGO_TARGET_DIR", "RUSTC"}
BUILD_SYSTEM_PATHS = (
    Path("/usr/local/sbin"),
    Path("/usr/local/bin"),
    Path("/usr/sbin"),
    Path("/usr/bin"),
)
BUILD_FIELDS = {
    "schema",
    "source_commit",
    "repository_root",
    "shared_root",
    "target_dir",
    "command",
    "environment",
    "environment_sha256",
    "cargo_path",
    "cargo_bytes",
    "cargo_sha256",
    "rustc_path",
    "rustc_bytes",
    "rustc_sha256",
    "started_at_ns",
    "ended_at_ns",
    "exit_code",
    "stdout_path",
    "stdout_bytes",
    "stdout_sha256",
    "stderr_path",
    "stderr_bytes",
    "stderr_sha256",
    "binary_path",
    "binary_bytes",
    "binary_sha256",
    "record_sha256",
}

ToolchainResolver = Callable[..., tuple[Path, Path]]
BuildRunner = Callable[..., Any]


@dataclass(frozen=True)
class AxeyumBuildCapture:
    """Private pre-attempt result of one exact-source build."""

    source_commit: str
    repository_root: Path
    shared_root: Path
    target_dir: Path
    command: tuple[str, ...]
    environment: dict[str, str]
    cargo_path: Path
    cargo_bytes: int
    cargo_sha256: str
    rustc_path: Path
    rustc_bytes: int
    rustc_sha256: str
    started_at_ns: int
    ended_at_ns: int
    exit_code: int
    stdout: bytes
    stderr: bytes
    binary: bytes


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _canonical_directory(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink():
        raise ContractError(f"invalid Axeyum-build {label} directory")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ContractError(f"invalid Axeyum-build {label} directory") from exc
    if resolved != path or not resolved.is_dir():
        raise ContractError(f"invalid Axeyum-build {label} directory")
    return resolved


def _canonical_executable(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.is_symlink():
        raise ContractError(f"invalid Axeyum-build {label} executable")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise ContractError(f"invalid Axeyum-build {label} executable") from exc
    if resolved != path or not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise ContractError(f"invalid Axeyum-build {label} executable")
    return resolved


def _account_environment() -> dict[str, str]:
    try:
        account = pwd.getpwuid(os.geteuid())
    except KeyError as exc:
        raise ContractError("unable to resolve Axeyum-build account") from exc
    home = _canonical_directory(Path(account.pw_dir), "home")
    cargo_home = _canonical_directory(home / ".cargo", "Cargo home")
    rustup_home = _canonical_directory(home / ".rustup", "Rustup home")
    _canonical_directory(cargo_home / "bin", "Cargo bin")
    for system_path in BUILD_SYSTEM_PATHS:
        _canonical_directory(system_path, "system PATH")
    return {
        "CARGO_HOME": str(cargo_home),
        "HOME": str(home),
        "LOGNAME": account.pw_name,
        "PATH": ":".join(
            [str(cargo_home / "bin"), *(str(path) for path in BUILD_SYSTEM_PATHS)]
        ),
        "RUSTUP_HOME": str(rustup_home),
        "USER": account.pw_name,
    }


def _resolve_toolchain(
    *, repository_root: Path, account_environment: dict[str, str]
) -> tuple[Path, Path]:
    """Resolve the active repository toolchain to non-proxy executables."""

    rustup_candidate = shutil.which("rustup", path=account_environment["PATH"])
    if rustup_candidate is None:
        raise ContractError("Axeyum-build rustup executable is unavailable")
    try:
        rustup = Path(rustup_candidate).resolve(strict=True)
    except OSError as exc:
        raise ContractError("Axeyum-build rustup executable is unavailable") from exc
    if not rustup.is_file() or not os.access(rustup, os.X_OK):
        raise ContractError("Axeyum-build rustup executable is invalid")

    resolved = []
    for tool in ("cargo", "rustc"):
        try:
            completed = subprocess.run(
                [str(rustup), "which", tool],
                cwd=repository_root,
                env={**BUILD_FIXED_ENVIRONMENT, **account_environment},
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
        except OSError as exc:
            raise ContractError(f"unable to resolve Axeyum-build {tool}") from exc
        if completed.returncode != 0:
            raise ContractError(f"unable to resolve Axeyum-build {tool}")
        try:
            rows = completed.stdout.decode("utf-8").splitlines()
        except UnicodeDecodeError as exc:
            raise ContractError(f"invalid Axeyum-build {tool} resolution") from exc
        if len(rows) != 1 or not rows[0]:
            raise ContractError(f"invalid Axeyum-build {tool} resolution")
        resolved.append(_canonical_executable(Path(rows[0]), tool))
    cargo, rustc = resolved
    if cargo.parent != rustc.parent:
        raise ContractError("Axeyum-build Cargo/Rust compiler toolchain mismatch")
    return cargo, rustc


def _build_environment(*, target_dir: Path, rustc_path: Path) -> dict[str, str]:
    environment = {
        **BUILD_FIXED_ENVIRONMENT,
        **_account_environment(),
        "CARGO_TARGET_DIR": str(target_dir),
        "RUSTC": str(rustc_path),
    }
    return _validate_build_environment(
        environment,
        target_dir=target_dir,
        rustc_path=rustc_path,
        inspect_current=True,
    )


def _validate_build_environment(
    environment: dict[str, str],
    *,
    target_dir: Path,
    rustc_path: Path,
    inspect_current: bool = False,
) -> dict[str, str]:
    if type(inspect_current) is not bool:
        raise ContractError("Axeyum-build environment inspection flag mismatch")
    expected_keys = set(BUILD_FIXED_ENVIRONMENT) | BUILD_ACCOUNT_KEYS | BUILD_DYNAMIC_KEYS
    if (
        not isinstance(environment, dict)
        or set(environment) != expected_keys
        or any(
            not isinstance(key, str)
            or not key
            or not isinstance(value, str)
            or not value
            for key, value in environment.items()
        )
    ):
        raise ContractError("Axeyum-build environment field mismatch")
    if any(environment.get(key) != value for key, value in BUILD_FIXED_ENVIRONMENT.items()):
        raise ContractError("Axeyum-build fixed environment drift")
    if environment["USER"] != environment["LOGNAME"]:
        raise ContractError("Axeyum-build account identity mismatch")
    home = Path(environment["HOME"])
    cargo_home = Path(environment["CARGO_HOME"])
    rustup_home = Path(environment["RUSTUP_HOME"])
    if (
        not home.is_absolute()
        or ".." in home.parts
        or cargo_home != home / ".cargo"
        or rustup_home != home / ".rustup"
        or environment["CARGO_TARGET_DIR"] != str(target_dir)
        or environment["RUSTC"] != str(rustc_path)
    ):
        raise ContractError("Axeyum-build environment path drift")
    expected_path = ":".join(
        [str(cargo_home / "bin"), *(str(path) for path in BUILD_SYSTEM_PATHS)]
    )
    if environment["PATH"] != expected_path:
        raise ContractError("Axeyum-build PATH drift")
    for component in environment["PATH"].split(":"):
        path = Path(component)
        if not component or not path.is_absolute() or ".." in path.parts:
            raise ContractError("Axeyum-build PATH is not canonical")
    if inspect_current:
        expected = {**BUILD_FIXED_ENVIRONMENT, **_account_environment()}
        observed = {
            key: value for key, value in environment.items() if key not in BUILD_DYNAMIC_KEYS
        }
        if observed != expected:
            raise ContractError("Axeyum-build current environment drift")
        _canonical_directory(target_dir, "target")
        _canonical_executable(rustc_path, "rustc")
    return environment


def _outside(path: Path, root: Path, message: str) -> None:
    try:
        path.relative_to(root)
    except ValueError:
        return
    raise ContractError(message)


def _execute_build(
    *, command: list[str], repository_root: Path, environment: dict[str, str]
) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        command,
        cwd=repository_root,
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def capture_axeyum_build(
    *,
    repository_root: Path,
    shared_root: Path,
    expected_commit: str,
    fixture_only: bool = False,
    toolchain_resolver: ToolchainResolver | None = None,
    build_runner: BuildRunner | None = None,
    now_ns: Callable[[], int] | None = None,
) -> AxeyumBuildCapture:
    """Build exact source privately and return bytes without shared mutation."""

    if type(fixture_only) is not bool:
        raise ContractError("Axeyum-build fixture flag mismatch")
    if not fixture_only and any(
        hook is not None for hook in (toolchain_resolver, build_runner, now_ns)
    ):
        raise ContractError("live Axeyum build requires registered runtime hooks")
    resolver = _resolve_toolchain if toolchain_resolver is None else toolchain_resolver
    runner = _execute_build if build_runner is None else build_runner
    clock = time.time_ns if now_ns is None else now_ns
    repository = repository_root.resolve(strict=True)
    shared = shared_root.resolve(strict=True)
    if not shared.is_dir() or shared.is_symlink():
        raise ContractError("invalid Axeyum-build shared root")
    if (
        not isinstance(expected_commit, str)
        or len(expected_commit) != 40
        or any(character not in "0123456789abcdef" for character in expected_commit)
    ):
        raise ContractError("invalid Axeyum-build source commit")
    if not fixture_only:
        require_exact_integrated_main(repository, expected_commit=expected_commit)

    account_environment = _account_environment()
    cargo, rustc = resolver(
        repository_root=repository,
        account_environment=account_environment,
    )
    cargo = _canonical_executable(cargo, "cargo")
    rustc = _canonical_executable(rustc, "rustc")
    tool_identities = {
        "cargo": (cargo.stat().st_size, sha256_file(cargo)),
        "rustc": (rustc.stat().st_size, sha256_file(rustc)),
    }

    with tempfile.TemporaryDirectory(prefix="axeyum-smtcomp-build-") as temporary:
        target = Path(temporary).resolve(strict=True)
        _outside(target, repository, "Axeyum-build target is inside repository")
        _outside(target, shared, "Axeyum-build target is inside shared root")
        environment = _build_environment(target_dir=target, rustc_path=rustc)
        actual_command = [str(cargo), *BUILD_COMMAND[1:]]
        started_at_ns = clock()
        try:
            completed = runner(
                command=actual_command,
                repository_root=repository,
                environment=environment,
            )
        except OSError as exc:
            raise ContractError("unable to execute exact-source Axeyum build") from exc
        ended_at_ns = clock()
        if (
            type(getattr(completed, "returncode", None)) is not int
            or not isinstance(getattr(completed, "stdout", None), bytes)
            or not isinstance(getattr(completed, "stderr", None), bytes)
        ):
            raise ContractError("invalid exact-source Axeyum build result")
        if completed.returncode != 0:
            raise ContractError("exact-source Axeyum build failed")
        if (
            type(started_at_ns) is not int
            or type(ended_at_ns) is not int
            or started_at_ns <= 0
            or ended_at_ns < started_at_ns
        ):
            raise ContractError("invalid exact-source Axeyum build timestamps")
        binary_path = target / "release" / "examples" / "smtcomp_cli"
        binary_path = _canonical_executable(binary_path, "smtcomp_cli")
        if binary_path.parent != target / "release" / "examples":
            raise ContractError("exact-source Axeyum build output path drift")
        binary = binary_path.read_bytes()
        if not binary:
            raise ContractError("exact-source Axeyum build output is empty")
        if not fixture_only:
            require_exact_integrated_main(repository, expected_commit=expected_commit)
        for label, path in (("cargo", cargo), ("rustc", rustc)):
            if tool_identities[label] != (path.stat().st_size, sha256_file(path)):
                raise ContractError(f"Axeyum-build {label} executable changed")
        return AxeyumBuildCapture(
            source_commit=expected_commit,
            repository_root=repository,
            shared_root=shared,
            target_dir=target,
            command=BUILD_COMMAND,
            environment=environment,
            cargo_path=cargo,
            cargo_bytes=tool_identities["cargo"][0],
            cargo_sha256=tool_identities["cargo"][1],
            rustc_path=rustc,
            rustc_bytes=tool_identities["rustc"][0],
            rustc_sha256=tool_identities["rustc"][1],
            started_at_ns=started_at_ns,
            ended_at_ns=ended_at_ns,
            exit_code=completed.returncode,
            stdout=completed.stdout,
            stderr=completed.stderr,
            binary=binary,
        )


def stage_axeyum_build(
    *,
    capture: AxeyumBuildCapture,
    attempt_root: Path,
    readiness: dict[str, Any],
) -> tuple[dict[str, Any], Path, str]:
    """Install private build products and seal the replayable observation."""

    if not isinstance(capture, AxeyumBuildCapture):
        raise ContractError("invalid Axeyum-build capture")
    attempt = attempt_root.resolve(strict=True)
    shared = capture.shared_root
    try:
        attempt.relative_to(shared)
    except ValueError as exc:
        raise ContractError("Axeyum-build attempt escapes shared root") from exc
    build_root = attempt / "build"
    inputs = attempt / "inputs"
    binaries = attempt / "binaries"
    for directory in (build_root, inputs, binaries):
        directory.mkdir(mode=0o755, parents=True, exist_ok=True)
    stdout_path = build_root / "axeyum-build.stdout"
    stderr_path = build_root / "axeyum-build.stderr"
    binary_path = binaries / "axeyum"
    atomic_install_bytes(build_root, stdout_path.name, capture.stdout)
    atomic_install_bytes(build_root, stderr_path.name, capture.stderr)
    atomic_install_bytes(binaries, binary_path.name, capture.binary)
    binary_path.chmod(0o555)
    with binary_path.open("rb") as handle:
        os.fsync(handle.fileno())
    observation = _sealed(
        {
            "schema": BUILD_SCHEMA,
            "source_commit": capture.source_commit,
            "repository_root": str(capture.repository_root),
            "shared_root": str(capture.shared_root),
            "target_dir": str(capture.target_dir),
            "command": list(capture.command),
            "environment": capture.environment,
            "environment_sha256": digest(capture.environment),
            "cargo_path": str(capture.cargo_path),
            "cargo_bytes": capture.cargo_bytes,
            "cargo_sha256": capture.cargo_sha256,
            "rustc_path": str(capture.rustc_path),
            "rustc_bytes": capture.rustc_bytes,
            "rustc_sha256": capture.rustc_sha256,
            "started_at_ns": capture.started_at_ns,
            "ended_at_ns": capture.ended_at_ns,
            "exit_code": capture.exit_code,
            "stdout_path": str(stdout_path.resolve(strict=True)),
            "stdout_bytes": len(capture.stdout),
            "stdout_sha256": _sha256_bytes(capture.stdout),
            "stderr_path": str(stderr_path.resolve(strict=True)),
            "stderr_bytes": len(capture.stderr),
            "stderr_sha256": _sha256_bytes(capture.stderr),
            "binary_path": str(binary_path.resolve(strict=True)),
            "binary_bytes": len(capture.binary),
            "binary_sha256": _sha256_bytes(capture.binary),
        }
    )
    atomic_install_json(inputs, "axeyum-build.json", observation)
    validated = validate_axeyum_build_observation(
        observation,
        attempt_root=attempt,
        readiness=readiness,
    )
    version = f"integrated-release-{validated['source_commit']}"
    return validated, binary_path.resolve(strict=True), version


def _valid_identity(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_axeyum_build_observation(
    observation: dict[str, Any],
    *,
    attempt_root: Path,
    readiness: dict[str, Any],
) -> dict[str, Any]:
    """Replay retained source/tool/output/binary authority without live tools."""

    if (
        not isinstance(observation, dict)
        or set(observation) != BUILD_FIELDS
        or observation.get("schema") != BUILD_SCHEMA
        or observation.get("record_sha256") != _sealed(observation)["record_sha256"]
    ):
        raise ContractError("Axeyum-build observation field/schema/seal mismatch")
    attempt = attempt_root.resolve(strict=True)
    repository = Path(observation.get("repository_root", ""))
    shared = Path(observation.get("shared_root", ""))
    target = Path(observation.get("target_dir", ""))
    cargo = Path(observation.get("cargo_path", ""))
    rustc = Path(observation.get("rustc_path", ""))
    if (
        not repository.is_absolute()
        or ".." in repository.parts
        or not shared.is_absolute()
        or ".." in shared.parts
        or not target.is_absolute()
        or ".." in target.parts
        or not cargo.is_absolute()
        or ".." in cargo.parts
        or not rustc.is_absolute()
        or ".." in rustc.parts
        or cargo.name != "cargo"
        or rustc.name != "rustc"
        or cargo.parent != rustc.parent
    ):
        raise ContractError("Axeyum-build authority path mismatch")
    try:
        attempt.relative_to(shared)
    except ValueError as exc:
        raise ContractError("Axeyum-build attempt/shared-root mismatch") from exc
    _outside(target, repository, "Axeyum-build target is inside repository")
    _outside(target, shared, "Axeyum-build target is inside shared root")
    if (
        observation.get("source_commit") != readiness.get("head_commit")
        or observation.get("repository_root") != readiness.get("repository_root")
        or observation.get("command") != list(BUILD_COMMAND)
        or observation.get("exit_code") != 0
        or type(observation.get("started_at_ns")) is not int
        or type(observation.get("ended_at_ns")) is not int
        or observation["started_at_ns"] <= 0
        or observation["ended_at_ns"] < observation["started_at_ns"]
    ):
        raise ContractError("Axeyum-build source/command/result mismatch")
    environment = observation.get("environment")
    if not isinstance(environment, dict):
        raise ContractError("Axeyum-build environment mismatch")
    _validate_build_environment(
        environment,
        target_dir=target,
        rustc_path=rustc,
        inspect_current=False,
    )
    if observation.get("environment_sha256") != digest(environment):
        raise ContractError("Axeyum-build environment identity mismatch")
    for label in ("cargo", "rustc"):
        if (
            type(observation.get(f"{label}_bytes")) is not int
            or observation[f"{label}_bytes"] <= 0
            or not _valid_identity(observation.get(f"{label}_sha256"))
        ):
            raise ContractError(f"Axeyum-build {label} identity mismatch")

    expected_paths = {
        "stdout": attempt / "build" / "axeyum-build.stdout",
        "stderr": attempt / "build" / "axeyum-build.stderr",
        "binary": attempt / "binaries" / "axeyum",
    }
    for label, expected in expected_paths.items():
        path = Path(observation.get(f"{label}_path", ""))
        if path != expected or path.is_symlink() or not path.is_file():
            raise ContractError(f"Axeyum-build {label} artifact path mismatch")
        if (
            type(observation.get(f"{label}_bytes")) is not int
            or observation[f"{label}_bytes"] < (1 if label == "binary" else 0)
            or path.stat().st_size != observation[f"{label}_bytes"]
            or not _valid_identity(observation.get(f"{label}_sha256"))
            or sha256_file(path) != observation[f"{label}_sha256"]
        ):
            raise ContractError(f"Axeyum-build {label} artifact drift")
    binary = expected_paths["binary"]
    if not os.access(binary, os.X_OK):
        raise ContractError("Axeyum-build binary is not executable")
    return observation
