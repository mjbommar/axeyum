#!/usr/bin/env python3
"""Independently re-derive and check the bounded-induction family operation.

`authoritative-mathlib-bounded-induction-factorial-family-v1` is the first
operation in `artifacts/autogenesis/operations.json` whose
`applicability.fact_ids` names more than one fact. Its producer/checker pair
(`bounded_induction_support` / `bounded_induction_operation.rs`) is
target-agnostic: `Eq.refl`, and where that is stuck, one bounded structural
induction over a discovered zero/succ binder plus one congruence rewrite
driven by the induction hypothesis.

This gate re-runs the checker example against all three targets the
operation names, from their tracked, hash-pinned external Mathlib exports,
and requires every receipt field to match the committed induction manifest
exactly. It also re-checks the ONE fact this operation actually settles
(`F:ml430-nat-descfactorial-one-d4856d4a`) is bound to it correctly, and
confirms the negative control -- the outcome-blind `n! = 0` mutation from the
same frozen census -- still declines. A checker that cannot fail is worse
than no checker, so this script fails loudly on any mismatch rather than
reporting completion alone.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import stat
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "artifacts/autogenesis/operations.json"
OPERATION_ID = "authoritative-mathlib-bounded-induction-factorial-family-v1"
SETTLED_FACT_ID = "F:ml430-nat-descfactorial-one-d4856d4a"
NEGATIVE_CONTROL_ROOT = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/coverage/"
    "26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1"
)
NEGATIVE_CONTROL_STREAM = NEGATIVE_CONTROL_ROOT / "streams/r046.ndjson"
NEGATIVE_CONTROL_TARGET = "Axeyum.Autogenesis.Coverage.r046"
NEGATIVE_CONTROL_FACT_ID = "F:ml430-mutation-7afa5ec620720a1501bf349d"


class FamilyError(RuntimeError):
    """The bounded-induction family no longer has its checked meaning."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise FamilyError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise FamilyError(f"expected JSON object: {path}")
    return value


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def parse_receipt(stdout: str) -> dict[str, str]:
    lines = stdout.splitlines()
    if (
        len(lines) != 3
        or not lines[0].startswith("BOUNDED_INDUCTION_OK|")
        or not lines[1].startswith("GOAL|")
        or not lines[2].startswith("PROOF|")
    ):
        raise FamilyError("bounded-induction checker emitted an invalid receipt shape")
    fields: dict[str, str] = {}
    for item in lines[0].split("|")[1:]:
        if "=" not in item:
            raise FamilyError("receipt field lacks '='")
        key, value = item.split("=", 1)
        if not key or key in fields or not value:
            raise FamilyError("receipt fields are empty or duplicated")
        fields[key] = value
    fields["goal"] = lines[1].removeprefix("GOAL|")
    fields["proof"] = lines[2].removeprefix("PROOF|")
    return fields


def run_checker(artifact: pathlib.Path, target: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [
            "cargo",
            "run",
            "--release",
            "-q",
            "-p",
            "axeyum-lean-import",
            "--example",
            "bounded_induction_operation",
            "--",
            str(artifact),
            target,
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )


def load_operation() -> dict[str, Any]:
    registry_checker = load_module(
        "bounded_induction_registry", ROOT / "scripts/validate-autogenesis-operations.py"
    )
    try:
        registry = registry_checker.load_registry(REGISTRY, ROOT)
    except registry_checker.RegistryError as error:
        raise FamilyError(f"operation registry is invalid: {error}") from error
    operations = {op["id"]: op for op in registry["operations"]}
    operation = operations.get(OPERATION_ID)
    if not isinstance(operation, dict):
        raise FamilyError(f"{OPERATION_ID} is not registered")
    return operation


def validate_external(external: dict[str, Any]) -> pathlib.Path:
    required = {"path", "sha256", "bytes", "records", "mode"}
    if set(external) != required:
        raise FamilyError("external artifact fields differ")
    path = pathlib.Path(external["path"])
    if (
        not path.is_file()
        or path.stat().st_size != external["bytes"]
        or sha256_file(path) != external["sha256"]
        or sum(1 for _ in path.open("rb")) != external["records"]
        or stat.S_IMODE(path.stat().st_mode) != int(external["mode"], 8)
    ):
        raise FamilyError(f"external artifact changed or missing: {path}")
    return path


def check_target(target: dict[str, Any], max_binders: int, max_inductions: int) -> None:
    fact_id = target["fact_id"]
    adapter = load(ROOT / target["statement_adapter_manifest"])
    induction = load(ROOT / target["induction_manifest"])
    op = induction.get("operation") or {}

    if (
        adapter.get("source_fact_id") != fact_id
        or induction.get("source_fact_id") != fact_id
        or induction.get("statement_adapter") != target["statement_adapter_manifest"]
        or op.get("target_definition") != target["target_definition"]
        or op.get("max_binders") != max_binders
        or op.get("max_inductions") != max_inductions
        or op.get("axioms") != 0
        or op.get("theorem_dependencies") != 0
        or op.get("target_dependency") is not False
    ):
        raise FamilyError(f"{fact_id}: adapter/induction manifest contract disagrees")

    fact = load(ROOT / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json"))
    statement = (fact.get("formal") or {}).get("statement")
    if (
        not isinstance(statement, str)
        or sha256_text(statement) != adapter.get("source_statement_sha256")
    ):
        raise FamilyError(f"{fact_id}: statement identity disagrees with its fact")

    artifact = validate_external(adapter["external_artifact"])
    completed = run_checker(artifact, target["target_definition"])
    if completed.returncode != 0:
        raise FamilyError(
            f"{fact_id}: bounded-induction replay failed: {completed.stderr.strip()}"
        )
    receipt = parse_receipt(completed.stdout.rstrip("\n"))
    expected = {
        "target": target["target_definition"],
        "goal_sha256": op["goal_sha256"],
        "proof_sha256": op["proof_sha256"],
        "target_content_sha256": op["target_content_sha256"],
        "binders_used": str(op["binders_used"]),
        "inductions_used": str(op["inductions_used"]),
        "max_binders": str(max_binders),
        "max_inductions": str(max_inductions),
        "declarations": str(op["admitted_declarations"]),
        "axioms": "0",
        "theorem_dependencies": "0",
        "target_dependency": "false",
        "ledger_writes": "0",
    }
    observed = {key: receipt.get(key) for key in expected}
    if observed != expected:
        raise FamilyError(f"{fact_id}: replayed receipt disagrees: {observed!r} != {expected!r}")
    if sha256_text(receipt["goal"]) != op["goal_sha256"]:
        raise FamilyError(f"{fact_id}: rendered goal digest disagrees")
    if sha256_text(receipt["proof"]) != op["proof_sha256"]:
        raise FamilyError(f"{fact_id}: rendered proof digest disagrees")


def check_settled_fact_binding(operation: dict[str, Any]) -> None:
    fact = load(
        ROOT / "artifacts/facts" / (SETTLED_FACT_ID.replace("F:", "F-") + ".json")
    )
    if fact.get("epistemic_status") != "proved" or fact.get("proof_route") != "kernel-lean":
        raise FamilyError(f"{SETTLED_FACT_ID}: not settled as expected")
    if fact.get("axiom_footprint") != []:
        raise FamilyError(f"{SETTLED_FACT_ID}: axiom footprint is not empty")
    rows = [
        row
        for row in fact.get("evidence", [])
        if isinstance(row, dict)
        and isinstance(row.get("checker_operation"), dict)
        and row["checker_operation"].get("id") == OPERATION_ID
    ]
    if len(rows) != 1:
        raise FamilyError(
            f"{SETTLED_FACT_ID}: expected exactly one evidence row bound to "
            f"{OPERATION_ID}, found {len(rows)}"
        )
    if rows[0].get("check_status") != "checked":
        raise FamilyError(f"{SETTLED_FACT_ID}: bound evidence row is not checked")
    for other_fact_id in operation["applicability"]["fact_ids"]:
        if other_fact_id == SETTLED_FACT_ID:
            continue
        other = load(
            ROOT / "artifacts/facts" / (other_fact_id.replace("F:", "F-") + ".json")
        )
        if other.get("epistemic_status") != "proved":
            raise FamilyError(
                f"{other_fact_id}: expected already-proved via its own operation"
            )
        bound_here = [
            row
            for row in other.get("evidence", [])
            if isinstance(row, dict)
            and isinstance(row.get("checker_operation"), dict)
            and row["checker_operation"].get("id") == OPERATION_ID
        ]
        if bound_here:
            raise FamilyError(
                f"{other_fact_id}: must not carry evidence bound to {OPERATION_ID} "
                "-- it already has proof credit through its own narrower operation, "
                "and this family operation is not claiming a second evidence row"
            )


def check_negative_control() -> None:
    if not NEGATIVE_CONTROL_STREAM.is_file():
        raise FamilyError(
            f"negative control stream missing: {NEGATIVE_CONTROL_STREAM}"
        )
    fact = load(
        ROOT
        / "artifacts/facts"
        / (NEGATIVE_CONTROL_FACT_ID.replace("F:", "F-") + ".json")
    )
    if fact.get("epistemic_status") != "open":
        raise FamilyError(
            f"{NEGATIVE_CONTROL_FACT_ID}: expected to remain open (it is FALSE)"
        )
    completed = run_checker(NEGATIVE_CONTROL_STREAM, NEGATIVE_CONTROL_TARGET)
    if completed.returncode == 0:
        raise FamilyError(
            "VOID: the negative control (a FALSE outcome-blind mutation) was "
            "ADMITTED by the bounded-induction checker. This census is void."
        )
    if "producer declined" not in completed.stderr:
        raise FamilyError(
            f"negative control failed for the wrong reason: {completed.stderr.strip()}"
        )
    # Also probe with a deliberately nonexistent path: a tool that ignores its
    # argument would pass every check above for the wrong reason.
    bogus = ROOT / "artifacts/autogenesis/does-not-exist-bounded-induction-probe.ndjson"
    if bogus.exists():
        raise FamilyError("probe path unexpectedly exists; pick a different name")
    bogus_completed = run_checker(bogus, NEGATIVE_CONTROL_TARGET)
    if bogus_completed.returncode == 0:
        raise FamilyError(
            "the bounded-induction checker ignored a nonexistent input path"
        )


def main() -> int:
    try:
        operation = load_operation()
        executor = operation["executor"]
        if executor["driver"] != "axeyum-lean-import/bounded-induction-multi-target-v1":
            raise FamilyError("operation driver changed")
        max_binders = executor["max_binders"]
        max_inductions = executor["max_inductions"]
        targets = executor["targets"]
        if len(targets) != 3:
            raise FamilyError("expected exactly three targets in this family")
        for target in targets:
            check_target(target, max_binders, max_inductions)
        check_settled_fact_binding(operation)
        check_negative_control()
        print(
            "AUTOGENESIS_BOUNDED_INDUCTION_FAMILY_OK|"
            f"operation={OPERATION_ID}|targets={len(targets)}|"
            f"settled_fact={SETTLED_FACT_ID}|"
            f"negative_control={NEGATIVE_CONTROL_FACT_ID}|"
            "negative_control_outcome=declined"
        )
        return 0
    except (
        OSError,
        KeyError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
        FamilyError,
    ) as error:
        print(f"AUTOGENESIS_BOUNDED_INDUCTION_FAMILY_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
