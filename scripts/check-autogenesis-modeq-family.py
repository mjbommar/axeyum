#!/usr/bin/env python3
"""Independently re-derive and check the ModEq-family operation.

`authoritative-mathlib-modeq-family-v1` is this ledger's SECOND general
autogenesis operation whose `applicability.fact_ids` names more than one
fact (the first is `authoritative-mathlib-bounded-induction-factorial-family-v1`).
Its producer/checker pair (`producers::modeq_family` / `modeq_family_operation.rs`)
is target-agnostic within one schema: `Int.ModEq n a b` (and `Nat.ModEq`/
`AxNat.ModEq`) unfolds transparently to `a % n = b % n`, so every one of the
four `integer-modular-equivalence` laws this operation covers
(`Int.ModEq.refl`, `Int.ModEq.symm`, `Int.ModEq.trans`, `Int.modEq_comm`) is
closed by a bounded search over `Eq.refl`/`Eq.symm`/`Eq.trans`/`Iff.intro`,
each reconstructed directly from `Eq.rec`/`Iff`'s own constructor -- never a
borrowed theorem, never a name lookup on the target or a sibling.

This gate re-runs the checker example against all four targets the operation
names, from their tracked, hash-pinned external Mathlib exports, and
requires every receipt field to match the committed candidate manifest
exactly. It also re-checks that each of the four facts this operation
settles is bound to it correctly -- exactly one checked evidence row each --
and that the checker declines on a nonexistent input path (a tool that
ignores its argument would pass every check above for the wrong reason).

The negative control for THIS producer's actual failure mode -- a candidate
that closes its goal by citing the target theorem itself, or any borrowed
theorem, rather than deriving everything from `Eq.rec`/`Iff.intro` -- is the
adversarial fixture in `crates/axeyum-lean-import/tests/
modeq_family_operation.rs` (`circularity_audit_rejects_direct_self_citation`),
re-run here rather than duplicated: mirroring it in Python would just be a
second, weaker copy of the same kernel-level check. A checker that cannot
fail is worse than no checker, so this script fails loudly on any mismatch
rather than reporting completion alone.
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
OPERATION_ID = "authoritative-mathlib-modeq-family-v1"
SETTLED_FACT_IDS = (
    "F:ml430-int-modeq-refl-30e15520",
    "F:ml430-int-modeq-symm-984a6e67",
    "F:ml430-int-modeq-trans-6d7863e0",
    "F:ml430-int-modeq-comm-1e4bcc07",
)


class FamilyError(RuntimeError):
    """The ModEq family no longer has its checked meaning."""


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
        or not lines[0].startswith("MODEQ_FAMILY_OK|")
        or not lines[1].startswith("GOAL|")
        or not lines[2].startswith("PROOF|")
    ):
        raise FamilyError("modeq-family checker emitted an invalid receipt shape")
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
            "modeq_family_operation",
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
        "modeq_family_registry", ROOT / "scripts/validate-autogenesis-operations.py"
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


def check_target(target: dict[str, Any], max_binders: int) -> None:
    fact_id = target["fact_id"]
    adapter = load(ROOT / target["statement_adapter_manifest"])
    modeq = load(ROOT / target["modeq_manifest"])
    op = modeq.get("operation") or {}

    if (
        adapter.get("source_fact_id") != fact_id
        or modeq.get("source_fact_id") != fact_id
        or modeq.get("statement_adapter") != target["statement_adapter_manifest"]
        or op.get("target_definition") != target["target_definition"]
        or op.get("max_binders") != max_binders
        or op.get("axioms") != 0
        or op.get("theorem_dependencies") != 0
        or op.get("target_dependency") is not False
    ):
        raise FamilyError(f"{fact_id}: adapter/modeq manifest contract disagrees")

    fact = load(ROOT / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json"))
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or sha256_text(statement) != adapter.get(
        "source_statement_sha256"
    ):
        raise FamilyError(f"{fact_id}: statement identity disagrees with its fact")

    artifact = validate_external(adapter["external_artifact"])
    completed = run_checker(artifact, target["target_definition"])
    if completed.returncode != 0:
        raise FamilyError(f"{fact_id}: modeq-family replay failed: {completed.stderr.strip()}")
    receipt = parse_receipt(completed.stdout.rstrip("\n"))
    expected = {
        "target": target["target_definition"],
        "goal_sha256": op["goal_sha256"],
        "proof_sha256": op["proof_sha256"],
        "target_content_sha256": op["target_content_sha256"],
        "binders_used": str(op["binders_used"]),
        "max_binders": str(max_binders),
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
    settled = set(SETTLED_FACT_IDS)
    all_named = operation["applicability"]["fact_ids"]
    missing_settled = settled - set(all_named)
    if missing_settled:
        raise FamilyError(
            f"SETTLED_FACT_IDS names fact(s) {sorted(missing_settled)} the "
            "operation no longer applies to"
        )
    for settled_fact_id in SETTLED_FACT_IDS:
        fact = load(ROOT / "artifacts/facts" / (settled_fact_id.replace("F:", "F-") + ".json"))
        if fact.get("epistemic_status") != "proved" or fact.get("proof_route") != "kernel-lean":
            raise FamilyError(f"{settled_fact_id}: not settled as expected")
        if fact.get("axiom_footprint") != []:
            raise FamilyError(f"{settled_fact_id}: axiom footprint is not empty")
        rows = [
            row
            for row in fact.get("evidence", [])
            if isinstance(row, dict)
            and isinstance(row.get("checker_operation"), dict)
            and row["checker_operation"].get("id") == OPERATION_ID
        ]
        if len(rows) != 1:
            raise FamilyError(
                f"{settled_fact_id}: expected exactly one evidence row bound to "
                f"{OPERATION_ID}, found {len(rows)}"
            )
        if rows[0].get("check_status") != "checked":
            raise FamilyError(f"{settled_fact_id}: bound evidence row is not checked")


def check_circularity_adversarial_control() -> None:
    """The negative control for THIS producer's actual failure mode: a
    candidate that closes its goal by citing the target theorem itself. See
    the module docstring for why this is re-run rather than duplicated in
    Python."""
    completed = subprocess.run(
        [
            "cargo",
            "test",
            "--release",
            "-q",
            "-p",
            "axeyum-lean-import",
            "--test",
            "modeq_family_operation",
            "--",
            "circularity_audit_rejects_direct_self_citation",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )
    if completed.returncode != 0:
        raise FamilyError(
            "VOID: the circularity adversarial fixture did not pass. This "
            f"census is void.\n{completed.stdout}\n{completed.stderr}"
        )
    if "1 passed" not in completed.stdout:
        raise FamilyError(
            f"the adversarial fixture ran a different test count than expected: {completed.stdout!r}"
        )


def check_bogus_path_declines(target_definition: str) -> None:
    bogus = ROOT / "artifacts/autogenesis/does-not-exist-modeq-family-probe.ndjson"
    if bogus.exists():
        raise FamilyError("probe path unexpectedly exists; pick a different name")
    completed = run_checker(bogus, target_definition)
    if completed.returncode == 0:
        raise FamilyError("the modeq-family checker ignored a nonexistent input path")


def main() -> int:
    try:
        operation = load_operation()
        executor = operation["executor"]
        if executor["driver"] != "axeyum-lean-import/modeq-family-multi-target-v1":
            raise FamilyError("operation driver changed")
        max_binders = executor["max_binders"]
        targets = executor["targets"]
        if len(targets) != 4:
            raise FamilyError("expected exactly four targets in this family")
        for target in targets:
            check_target(target, max_binders)
        check_settled_fact_binding(operation)
        check_circularity_adversarial_control()
        check_bogus_path_declines(targets[0]["target_definition"])
        print(
            "AUTOGENESIS_MODEQ_FAMILY_OK|"
            f"operation={OPERATION_ID}|targets={len(targets)}|"
            f"settled_facts={','.join(SETTLED_FACT_IDS)}|"
            "circularity_adversarial_control=rejected|"
            "bogus_path_control=declined"
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
        print(f"AUTOGENESIS_MODEQ_FAMILY_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
