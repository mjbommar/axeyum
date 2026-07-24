"""Mainline-gated cell admission for credited full-population execution.

F2 deliberately publishes ``launch_authorized=false``.  F3 therefore needs a
separate, integrated acceptance record before any solver cell may start.  This
module builds and durably replays that record and the exact solver-order prior
result prefix.  It is process-free: no host probe, launch, stop, or NAS recovery
is performed here.
"""

from __future__ import annotations

import copy
import json
import subprocess
import time
from pathlib import Path
from typing import Any

from full_population import SOLVER_IDS
from full_prepare import validate_full_preparation
from full_result import load_full_cell_result
from resume_contract import ContractError, canonical_bytes, digest
from resume_fs import read_canonical_json


ACCEPTANCE_SCHEMA = "axeyum.smtcomp-credited-full-preparation-acceptance.v1"
ADMISSION_SCHEMA = "axeyum.smtcomp-credited-full-cell-admission.v1"
LIVE_ACCEPTANCE_RELATIVE = Path(
    "docs/plan/smtcomp-credited-full-preparation-acceptance-v1.json"
)
ACCEPTANCE_FIELDS = {
    "schema",
    "status",
    "fixture_only",
    "execution_source_commit",
    "preparation_record_sha256",
    "selection_record_sha256",
    "record_sha256",
}
PRIOR_RESULT_FIELDS = {
    "solver_id",
    "completion_record_sha256",
    "safe_to_continue",
}
ADMISSION_FIELDS = {
    "schema",
    "fixture_only",
    "solver_id",
    "mainline_acceptance_commit",
    "mainline_acceptance_path",
    "acceptance_record_sha256",
    "preparation_record_sha256",
    "selection_record_sha256",
    "composition_record_sha256",
    "run_identity_sha256",
    "plan_sha256",
    "schedule_record_sha256",
    "prior_cell_results",
    "admitted_at_ns",
    "record_sha256",
}


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _sealed(value: dict[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(value)
    result.pop("record_sha256", None)
    result["record_sha256"] = digest(result)
    return result


def _is_hex(value: Any, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _is_sha256(value: Any) -> bool:
    return _is_hex(value, 64)


def _is_git_oid(value: Any) -> bool:
    return _is_hex(value, 40)


def _git(root: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(
            ["git", *args], cwd=root, stderr=subprocess.STDOUT
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError(f"unable to inspect admission Git state: {' '.join(args)}") from exc


def _commit(root: Path, revision: str) -> str:
    value = _git(root, "rev-parse", "--verify", f"{revision}^{{commit}}")
    try:
        result = value.decode("ascii").strip()
    except UnicodeDecodeError as exc:
        raise ContractError("admission Git commit is non-ASCII") from exc
    _expect(_is_git_oid(result), "admission Git commit identity mismatch")
    return result


def _require_ancestor(root: Path, ancestor: str, descendant: str) -> None:
    try:
        subprocess.check_call(
            ["git", "merge-base", "--is-ancestor", ancestor, descendant],
            cwd=root,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ContractError(
            "accepted execution revision is not an ancestor of acceptance"
        ) from exc


def _clean_main(root: Path) -> str:
    head = _commit(root, "HEAD")
    origin = _commit(root, "origin/main")
    _expect(head == origin, "live cell admission is not based on origin/main")
    _expect(
        _git(root, "status", "--porcelain=v1", "--untracked-files=all") == b"",
        "live cell admission repository is dirty",
    )
    return head


def build_full_preparation_acceptance(
    *,
    execution_source_commit: str,
    preparation_record_sha256: str,
    selection_record_sha256: str,
    fixture_only: bool = False,
) -> dict[str, Any]:
    """Build the record the integration owner accepts before F3 admission."""

    return validate_full_preparation_acceptance(
        _sealed(
            {
                "schema": ACCEPTANCE_SCHEMA,
                "status": "accepted",
                "fixture_only": fixture_only,
                "execution_source_commit": execution_source_commit,
                "preparation_record_sha256": preparation_record_sha256,
                "selection_record_sha256": selection_record_sha256,
            }
        )
    )


def validate_full_preparation_acceptance(
    acceptance: dict[str, Any],
) -> dict[str, Any]:
    _expect(
        isinstance(acceptance, dict)
        and set(acceptance) == ACCEPTANCE_FIELDS
        and acceptance.get("schema") == ACCEPTANCE_SCHEMA
        and acceptance.get("status") == "accepted"
        and type(acceptance.get("fixture_only")) is bool
        and acceptance.get("record_sha256") == _sealed(acceptance)["record_sha256"],
        "full preparation acceptance field/schema/seal mismatch",
    )
    _expect(
        _is_git_oid(acceptance.get("execution_source_commit")),
        "full preparation acceptance commit mismatch",
    )
    for field in ("preparation_record_sha256", "selection_record_sha256"):
        _expect(_is_sha256(acceptance.get(field)), "full preparation acceptance hash mismatch")
    return acceptance


def _component_records(attempt: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    selection = read_canonical_json(
        attempt / "inputs" / "full-selection-preparation.json"
    )
    composition = read_canonical_json(
        attempt / "inputs" / "full-cell-composition.json"
    )
    readiness = read_canonical_json(attempt / "inputs" / "full-readiness.json")
    _expect(
        isinstance(selection, dict)
        and isinstance(composition, dict)
        and isinstance(readiness, dict),
        "full cell admission component type mismatch",
    )
    return selection, composition, readiness


def _prior_results(
    *,
    prior_result_roots: dict[str, Path],
    solver_id: str,
    expected_logic_counts: dict[str, int],
    preparation_record_sha256: str,
    selection_record_sha256: str,
    fixture_only: bool,
) -> tuple[list[dict[str, Any]], int]:
    solver_index = SOLVER_IDS.index(solver_id)
    _expect(
        tuple(prior_result_roots) == SOLVER_IDS[:solver_index],
        "full cell admission prior-result order mismatch",
    )
    rows = []
    latest_published_at_ns = 0
    for prior_solver in SOLVER_IDS[:solver_index]:
        completion, _records = load_full_cell_result(
            prior_result_roots[prior_solver],
            expected_logic_counts=expected_logic_counts,
        )
        _expect(
            completion["solver_id"] == prior_solver
            and completion["preparation_record_sha256"]
            == preparation_record_sha256
            and completion["selection_record_sha256"] == selection_record_sha256
            and completion["fixture_only"] is fixture_only
            and completion["safe_to_continue"] is True,
            "full cell admission prior-result authority mismatch",
        )
        rows.append(
            {
                "solver_id": prior_solver,
                "completion_record_sha256": completion["record_sha256"],
                "safe_to_continue": True,
            }
        )
        latest_published_at_ns = max(
            latest_published_at_ns, completion["published_at_ns"]
        )
    return rows, latest_published_at_ns


def _live_acceptance(
    *, repository_root: Path, acceptance: dict[str, Any], acceptance_path: Path
) -> tuple[str, str]:
    root = repository_root.resolve(strict=True)
    path = acceptance_path.resolve(strict=True)
    expected = (root / LIVE_ACCEPTANCE_RELATIVE).resolve()
    _expect(
        path == expected and path.is_file() and not path.is_symlink(),
        "live preparation acceptance path mismatch",
    )
    commit = _clean_main(root)
    _require_ancestor(root, acceptance["execution_source_commit"], commit)
    relative = path.relative_to(root).as_posix()
    _expect(
        path.read_bytes() == canonical_bytes(acceptance)
        and _git(root, "show", f"{commit}:{relative}") == canonical_bytes(acceptance),
        "live preparation acceptance is not integrated byte-exactly",
    )
    return commit, relative


def build_full_cell_admission(
    preparation_root: Path,
    *,
    repository_root: Path,
    solver_id: str,
    expected_logic_counts: dict[str, int],
    prior_result_roots: dict[str, Path],
    acceptance: dict[str, Any],
    acceptance_path: Path | None = None,
    inspect_shared_root: bool = True,
    admitted_at_ns: int | None = None,
) -> dict[str, Any]:
    """Admit exactly the next empty solver cell after mainline acceptance."""

    _expect(solver_id in SOLVER_IDS, "full cell admission solver identity mismatch")
    accepted = validate_full_preparation_acceptance(acceptance)
    solver_index = SOLVER_IDS.index(solver_id)
    preparation = validate_full_preparation(
        preparation_root,
        repository_root=repository_root,
        inspect_shared_root=inspect_shared_root,
        allowed_execution_solver_ids=SOLVER_IDS[:solver_index],
    )
    attempt = preparation_root.resolve(strict=True)
    selection, composition, readiness = _component_records(attempt)
    _expect(
        accepted["fixture_only"] is preparation["fixture_only"]
        and accepted["preparation_record_sha256"] == preparation["record_sha256"]
        and accepted["selection_record_sha256"] == selection["record_sha256"]
        and accepted["execution_source_commit"] == readiness["head_commit"],
        "full cell admission acceptance/preparation drift",
    )
    if preparation["fixture_only"]:
        _expect(acceptance_path is None, "fixture admission names a live acceptance path")
        mainline_commit = accepted["execution_source_commit"]
        mainline_path = None
    else:
        _expect(acceptance_path is not None, "live admission lacks acceptance path")
        mainline_commit, mainline_path = _live_acceptance(
            repository_root=repository_root,
            acceptance=accepted,
            acceptance_path=acceptance_path,
        )
    prior_rows, latest_prior = _prior_results(
        prior_result_roots=prior_result_roots,
        solver_id=solver_id,
        expected_logic_counts=expected_logic_counts,
        preparation_record_sha256=preparation["record_sha256"],
        selection_record_sha256=selection["record_sha256"],
        fixture_only=preparation["fixture_only"],
    )
    cell = composition["cells"][solver_index]
    _expect(cell.get("solver_id") == solver_id, "full cell admission composition order drift")
    timestamp = time.time_ns() if admitted_at_ns is None else admitted_at_ns
    _expect(
        type(timestamp) is int
        and timestamp >= max(preparation["prepared_at_ns"], latest_prior),
        "full cell admission timestamp mismatch",
    )
    admission = _sealed(
        {
            "schema": ADMISSION_SCHEMA,
            "fixture_only": preparation["fixture_only"],
            "solver_id": solver_id,
            "mainline_acceptance_commit": mainline_commit,
            "mainline_acceptance_path": mainline_path,
            "acceptance_record_sha256": accepted["record_sha256"],
            "preparation_record_sha256": preparation["record_sha256"],
            "selection_record_sha256": selection["record_sha256"],
            "composition_record_sha256": composition["record_sha256"],
            "run_identity_sha256": cell["run_identity_sha256"],
            "plan_sha256": cell["plan_sha256"],
            "schedule_record_sha256": cell["schedule_record_sha256"],
            "prior_cell_results": prior_rows,
            "admitted_at_ns": timestamp,
        }
    )
    return validate_full_cell_admission(
        admission,
        preparation_root=preparation_root,
        repository_root=repository_root,
        expected_logic_counts=expected_logic_counts,
        prior_result_roots=prior_result_roots,
        acceptance=accepted,
        inspect_shared_root=inspect_shared_root,
    )


def validate_full_cell_admission(
    admission: dict[str, Any],
    *,
    preparation_root: Path,
    repository_root: Path,
    expected_logic_counts: dict[str, int],
    prior_result_roots: dict[str, Path],
    acceptance: dict[str, Any] | None = None,
    inspect_shared_root: bool = True,
) -> dict[str, Any]:
    """Durably replay admission from its recorded mainline Git object."""

    _expect(
        isinstance(admission, dict)
        and set(admission) == ADMISSION_FIELDS
        and admission.get("schema") == ADMISSION_SCHEMA
        and admission.get("solver_id") in SOLVER_IDS
        and type(admission.get("fixture_only")) is bool
        and admission.get("record_sha256") == _sealed(admission)["record_sha256"],
        "full cell admission field/schema/seal mismatch",
    )
    solver_id = admission["solver_id"]
    solver_index = SOLVER_IDS.index(solver_id)
    preparation = validate_full_preparation(
        preparation_root,
        repository_root=repository_root,
        inspect_shared_root=inspect_shared_root,
        allowed_execution_solver_ids=SOLVER_IDS[: solver_index + 1],
    )
    attempt = preparation_root.resolve(strict=True)
    selection, composition, readiness = _component_records(attempt)
    if admission["fixture_only"]:
        _expect(acceptance is not None, "fixture admission replay lacks acceptance")
        accepted = validate_full_preparation_acceptance(acceptance)
        _expect(
            admission["mainline_acceptance_path"] is None,
            "fixture admission carries a live acceptance path",
        )
    else:
        path = admission.get("mainline_acceptance_path")
        _expect(isinstance(path, str), "live admission acceptance path mismatch")
        _expect(
            path == LIVE_ACCEPTANCE_RELATIVE.as_posix(),
            "live admission acceptance path mismatch",
        )
        root = repository_root.resolve(strict=True)
        commit = _commit(root, admission["mainline_acceptance_commit"])
        raw = _git(
            root,
            "show",
            f"{commit}:{path}",
        )
        try:
            accepted = validate_full_preparation_acceptance(json.loads(raw))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ContractError("live admission acceptance Git object is malformed") from exc
        _expect(raw == canonical_bytes(accepted), "live admission acceptance is non-canonical")
        _require_ancestor(root, accepted["execution_source_commit"], commit)
    _expect(
        accepted["fixture_only"] is preparation["fixture_only"]
        and admission["acceptance_record_sha256"] == accepted["record_sha256"]
        and accepted["execution_source_commit"] == readiness["head_commit"]
        and accepted["preparation_record_sha256"] == preparation["record_sha256"]
        and accepted["selection_record_sha256"] == selection["record_sha256"],
        "full cell admission acceptance/preparation drift",
    )
    prior_rows, latest_prior = _prior_results(
        prior_result_roots=prior_result_roots,
        solver_id=solver_id,
        expected_logic_counts=expected_logic_counts,
        preparation_record_sha256=preparation["record_sha256"],
        selection_record_sha256=selection["record_sha256"],
        fixture_only=preparation["fixture_only"],
    )
    cell = composition["cells"][solver_index]
    _expect(
        admission["fixture_only"] is preparation["fixture_only"]
        and accepted["fixture_only"] is preparation["fixture_only"]
        and admission["acceptance_record_sha256"] == accepted["record_sha256"]
        and admission["mainline_acceptance_commit"]
        == (
            accepted["execution_source_commit"]
            if admission["fixture_only"]
            else admission["mainline_acceptance_commit"]
        )
        and accepted["execution_source_commit"] == readiness["head_commit"]
        and admission["preparation_record_sha256"] == preparation["record_sha256"]
        and admission["selection_record_sha256"] == selection["record_sha256"]
        and admission["composition_record_sha256"] == composition["record_sha256"]
        and admission["run_identity_sha256"] == cell["run_identity_sha256"]
        and admission["plan_sha256"] == cell["plan_sha256"]
        and admission["schedule_record_sha256"] == cell["schedule_record_sha256"]
        and admission["prior_cell_results"] == prior_rows
        and all(set(row) == PRIOR_RESULT_FIELDS for row in prior_rows)
        and type(admission["admitted_at_ns"]) is int
        and admission["admitted_at_ns"]
        >= max(preparation["prepared_at_ns"], latest_prior),
        "full cell admission replay drift",
    )
    return admission
