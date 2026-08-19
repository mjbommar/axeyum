#!/usr/bin/env python3
"""Execute and replay one machine-selected authoritative Autogenesis operation.

The frontier chooses the fact; the operation registry chooses the executable,
input artifact, budget, and expected evidence label. Callers supply none of
those fields. The normalized receipt binds the clean Git commit, frontier,
registry, fact, input bytes, and independently rechecked evidence observation.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import pathlib
import re
import stat
import subprocess
import sys
import tempfile
from collections.abc import Callable
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
FRONTIER_SCRIPT = ROOT / "scripts/fact-frontier.py"
REGISTRY_SCRIPT = ROOT / "scripts/validate-autogenesis-operations.py"
INDUCTION_PROPOSER = ROOT / "scripts/autogenesis-induction-proposer.py"
APPLY_PROPOSER = ROOT / "scripts/autogenesis-apply-proposer.py"
APPLY_TRANSACTION_SCRIPT = ROOT / "scripts/apply-autogenesis-fact-transaction.py"
READINESS_SCRIPT = ROOT / "scripts/create-autogenesis-readiness-delta.py"
STATEMENT_REFLEXIVITY_CHECKER = (
    ROOT / "scripts/check-autogenesis-statement-reflexivity.py"
)
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
EVIDENCE_RE = re.compile(
    r"^;\s*evidence\s+kind=(\S+)\s+certified=(\S+)\s+"
    r"recheck=(\S+)\s+arena=(\S+)\s+ms=(\d+)\s*$",
    re.MULTILINE,
)


class ExecutionError(RuntimeError):
    """Selection, execution, or receipt replay was not exact and admissible."""


def load_module(name: str, path: pathlib.Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ExecutionError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def byte_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def statement_reflexivity_contract(
    operation: dict[str, Any], fact: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any]]:
    executor = operation["executor"]
    adapter = json.loads((ROOT / executor["statement_adapter_manifest"]).read_text())
    reflexivity = json.loads((ROOT / executor["reflexivity_manifest"]).read_text())
    evidence = reflexivity.get("operation") or {}
    statement = (fact.get("formal") or {}).get("statement")
    if (
        adapter.get("source_fact_id") != fact.get("id")
        or reflexivity.get("source_fact_id") != fact.get("id")
        or reflexivity.get("statement_adapter")
        != executor["statement_adapter_manifest"]
        or not isinstance(statement, str)
        or byte_digest(statement.encode()) != adapter.get("source_statement_sha256")
        or evidence.get("target_definition") != executor["target_definition"]
        or evidence.get("max_binders") != executor["max_binders"]
        or evidence.get("max_constructed_nodes")
        != executor["max_constructed_nodes"]
    ):
        raise ExecutionError("statement-reflexivity source contract is inconsistent")
    return adapter, reflexivity


def expected_statement_reflexivity_observation(
    operation: dict[str, Any], fact: dict[str, Any]
) -> dict[str, Any]:
    adapter, reflexivity = statement_reflexivity_contract(operation, fact)
    evidence = reflexivity["operation"]
    return {
        "verdict": "proved",
        "evidence_label": operation["executor"]["expected_evidence_label"],
        "goal_sha256": evidence["goal_sha256"],
        "proof_sha256": evidence["proof_sha256"],
        "target_content_sha256": evidence["target_content_sha256"],
        "external_artifact_sha256": adapter["external_artifact"]["sha256"],
        "binders": evidence["binders"],
        "constructed_nodes": evidence["constructed_nodes"],
        "max_binders": evidence["max_binders"],
        "max_constructed_nodes": evidence["max_constructed_nodes"],
        "admitted_declarations": evidence["admitted_declarations"],
        "axiom_footprint": [],
        "retained_answer_dependencies": [],
        "target_dependency": False,
        "ledger_writes": 0,
    }


def run_statement_reflexivity_registered(
    operation: dict[str, Any],
) -> dict[str, Any]:
    executor = operation["executor"]
    frontier_module = load_module(
        "frontier_for_statement_reflexivity_execution", FRONTIER_SCRIPT
    )
    fact = frontier_module.load().get(executor["input_fact_id"])
    if not isinstance(fact, dict):
        raise ExecutionError("statement-reflexivity input fact is absent")
    adapter, reflexivity = statement_reflexivity_contract(operation, fact)
    external = adapter["external_artifact"]
    artifact = pathlib.Path(external["path"])
    if not artifact.is_file():
        raise ExecutionError("registered statement artifact is unavailable")
    payload = artifact.read_bytes()
    if (
        len(payload) != external["bytes"]
        or byte_digest(payload) != external["sha256"]
        or len(payload.splitlines()) != external["records"]
        or stat.S_IMODE(artifact.stat().st_mode) != int(external["mode"], 8)
    ):
        raise ExecutionError("registered statement artifact identity changed")
    command = [
        "cargo",
        "run",
        "-q",
        "-p",
        "axeyum-lean-import",
        "--example",
        "statement_reflexivity_operation",
        "--",
        str(artifact),
        executor["target_definition"],
    ]
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=executor["timeout_seconds"],
        )
    except subprocess.TimeoutExpired as error:
        raise ExecutionError(
            "statement-reflexivity operation exceeded its timeout"
        ) from error
    if completed.returncode != 0:
        diagnostic = completed.stderr.strip().splitlines()
        suffix = diagnostic[-1] if diagnostic else "no diagnostic"
        raise ExecutionError(
            f"statement-reflexivity executor exited {completed.returncode}: {suffix}"
        )
    checker = load_module(
        "statement_reflexivity_checker_for_execution",
        STATEMENT_REFLEXIVITY_CHECKER,
    )
    try:
        receipt = checker.parse_receipt(completed.stdout.rstrip("\n"))
        checker.validate_receipt(reflexivity, receipt)
    except checker.ReflexivityError as error:
        raise ExecutionError(f"statement-reflexivity receipt failed: {error}") from error
    expected_keys = {
        "target",
        "goal_sha256",
        "proof_sha256",
        "target_content_sha256",
        "binders",
        "constructed_nodes",
        "max_binders",
        "max_nodes",
        "declarations",
        "axioms",
        "theorem_dependencies",
        "target_dependency",
        "ledger_writes",
        "goal",
        "proof",
    }
    if set(receipt) != expected_keys:
        raise ExecutionError("statement-reflexivity receipt fields differ from v1")
    observation = expected_statement_reflexivity_observation(operation, fact)
    observed_counts = {
        "binders": receipt["binders"],
        "constructed_nodes": receipt["constructed_nodes"],
        "max_binders": receipt["max_binders"],
        "max_constructed_nodes": receipt["max_nodes"],
        "admitted_declarations": receipt["declarations"],
        "axioms": receipt["axioms"],
        "theorem_dependencies": receipt["theorem_dependencies"],
        "target_dependency": receipt["target_dependency"],
        "ledger_writes": receipt["ledger_writes"],
    }
    expected_counts = {
        "binders": str(observation["binders"]),
        "constructed_nodes": str(observation["constructed_nodes"]),
        "max_binders": str(observation["max_binders"]),
        "max_constructed_nodes": str(observation["max_constructed_nodes"]),
        "admitted_declarations": str(observation["admitted_declarations"]),
        "axioms": "0",
        "theorem_dependencies": "0",
        "target_dependency": "false",
        "ledger_writes": "0",
    }
    if observed_counts != expected_counts:
        raise ExecutionError("statement-reflexivity assurance counters changed")
    return observation


def verify_content_addressed(value: dict[str, Any], field: str, label: str) -> str:
    claimed = value.get(field)
    unsigned = dict(value)
    unsigned.pop(field, None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ExecutionError(f"{label} digest is missing or invalid")
    return claimed


def clean_commit() -> str:
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    if status:
        raise ExecutionError("authoritative execution requires a clean checkout")
    commit = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if not COMMIT_RE.fullmatch(commit):
        raise ExecutionError("checkout HEAD is not a full Git commit identity")
    return commit


def selected_inputs(
    frontier: dict[str, Any],
    facts: dict[str, dict[str, Any]] | None = None,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    frontier_module = load_module("autogenesis_frontier_for_execution", FRONTIER_SCRIPT)
    registry_module = load_module("autogenesis_registry_for_execution", REGISTRY_SCRIPT)
    if facts is None:
        facts = frontier_module.load()
    try:
        frontier_module.verify_machine_frontier(frontier, facts)
        registry = registry_module.load_registry(
            ROOT / "artifacts/autogenesis/operations.json", ROOT
        )
    except (frontier_module.FrontierError, registry_module.RegistryError) as error:
        raise ExecutionError(f"frontier or operation registry is invalid: {error}") from error

    selected = (frontier.get("selection") or {}).get("selected_fact_id")
    admissible = (frontier.get("selection") or {}).get("admissible_fact_ids")
    if not isinstance(selected, str) or admissible != [selected]:
        raise ExecutionError("executor requires exactly one admissible selected fact")
    fact = facts.get(selected)
    if not isinstance(fact, dict):
        raise ExecutionError("selected fact is absent from the authoritative ledger")
    matches = [
        operation
        for operation in registry["operations"]
        if operation["scope"] == "authoritative"
        and selected in operation["applicability"]["fact_ids"]
        and fact["formal"]["language"]
        in operation["applicability"]["formal_languages"]
        and fact["formal"]["fragment"] in operation["applicability"]["fragments"]
    ]
    if len(matches) != 1:
        raise ExecutionError(
            f"selected fact has {len(matches)} exact authoritative operations; expected one"
        )
    operation = matches[0]
    entry = next(
        (row for row in frontier["entries"] if row.get("fact_id") == selected), None
    )
    if not isinstance(entry, dict) or entry.get("registered_operation_ids") != [
        operation["id"]
    ]:
        raise ExecutionError("frontier selection does not bind the exact operation")
    return fact, operation, registry


def parse_observation(stdout: str) -> dict[str, Any]:
    matches = list(EVIDENCE_RE.finditer(stdout))
    if len(matches) != 1:
        raise ExecutionError(
            f"executor expected exactly one evidence line, observed {len(matches)}"
        )
    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    if not lines:
        raise ExecutionError("executor produced no verdict")
    match = matches[0]
    return {
        "verdict": lines[-1],
        "evidence_label": match.group(1),
        "certified": match.group(2) == "1",
        "recheck": match.group(3),
        "arena": match.group(4),
    }


def run_smt_registered(operation: dict[str, Any]) -> dict[str, Any]:
    executor = operation["executor"]
    if executor["driver"] != "axeyum-bench/smtcomp-evidence-v1":
        raise ExecutionError(f"unsupported execution driver {executor['driver']!r}")
    artifact = executor["input_artifact"]
    if os.environ.get("AXEYUM_SMTCOMP_CLI"):
        raise ExecutionError(
            "authoritative execution forbids the AXEYUM_SMTCOMP_CLI override"
        )
    command = [
        "cargo",
        "run",
        "--release",
        "-q",
        "-p",
        "axeyum-bench",
        "--example",
        "smtcomp_cli",
        "--",
        "--evidence",
        artifact,
    ]
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=executor["timeout_seconds"],
        )
    except subprocess.TimeoutExpired as error:
        raise ExecutionError(
            f"registered operation exceeded {executor['timeout_seconds']} seconds"
        ) from error
    if completed.returncode != 0:
        diagnostic = completed.stderr.strip().splitlines()
        suffix = diagnostic[-1] if diagnostic else "no diagnostic"
        raise ExecutionError(
            f"registered executor exited {completed.returncode}: {suffix}"
        )
    return parse_observation(completed.stdout)


def formal_type(fact: dict[str, Any]) -> str:
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or " : " not in statement:
        raise ExecutionError("kernel operation fact has no theorem type")
    return statement.split(" : ", 1)[1]


def theorem_candidate(fact_sha256: str, role: str) -> str:
    if not re.fullmatch(r"[0-9a-f]{64}", fact_sha256):
        raise ExecutionError("candidate source fact digest is invalid")
    return f"Autogenesis.Authoritative.E{fact_sha256[:16]}.{role}"


def induction_catalog(
    fact: dict[str, Any], candidate: str, denied_theorems: list[str]
) -> dict[str, Any]:
    arity = len((fact.get("formal") or {}).get("free_symbols") or [])
    if arity < 1:
        raise ExecutionError("kernel executor target has no formal binder")
    catalog: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-authoritative-kernel-goal-catalog",
        "phase": "pre_b",
        "proof_bodies_included": False,
        "denied_theorems": denied_theorems,
        "target": {
            "name": candidate,
            "arity": arity,
            "canonical_type": formal_type(fact),
            "source_fact_id": fact["id"],
        },
    }
    catalog["catalog_sha256"] = digest(catalog)
    return catalog


def load_episode_trigger(
    *,
    bundle: pathlib.Path,
    frontier: dict[str, Any],
    facts: dict[str, dict[str, Any]],
    registry: dict[str, Any],
    operation: dict[str, Any],
) -> dict[str, Any]:
    paths = {
        "frontier_before": bundle / "frontier-before.json",
        "execution": bundle / "execution.json",
        "transaction": bundle / "transaction.json",
        "event": bundle / "admission-event.json",
        "readiness": bundle / "readiness.json",
    }
    missing = sorted(name for name, path in paths.items() if not path.is_file())
    if missing:
        raise ExecutionError(f"episode trigger bundle is missing {missing}")
    try:
        values = {name: json.loads(path.read_text()) for name, path in paths.items()}
    except (OSError, json.JSONDecodeError) as error:
        raise ExecutionError(f"episode trigger bundle is unreadable: {error}") from error
    premise_execution = values["execution"]
    frontier_before = values["frontier_before"]
    transaction = values["transaction"]
    event = values["event"]
    readiness = values["readiness"]
    execution_sha = verify_content_addressed(
        premise_execution, "execution_sha256", "premise execution"
    )
    transaction_sha = verify_content_addressed(
        transaction, "transaction_sha256", "premise transaction"
    )
    event_sha = verify_content_addressed(event, "event_sha256", "premise event")
    readiness_sha = verify_content_addressed(
        readiness, "readiness_delta_sha256", "premise readiness"
    )
    executor = operation["executor"]
    premise_id = executor["premise_fact_id"]
    target_id = executor["input_fact_id"]
    premise_operation_id = executor["premise_operation_id"]
    premise_identity = premise_execution.get("identity")
    transaction_identity = transaction.get("identity")
    readiness_identity = readiness.get("identity")
    if not all(
        isinstance(value, dict)
        for value in (premise_identity, transaction_identity, readiness_identity)
    ):
        raise ExecutionError("episode trigger identities are malformed")
    registry_sha = digest(registry)
    if (
        premise_identity.get("fact_id") != premise_id
        or premise_identity.get("operation_id") != premise_operation_id
        or premise_identity.get("operation_registry_sha256") != registry_sha
        or transaction_identity.get("fact_id") != premise_id
        or transaction_identity.get("execution_sha256") != execution_sha
        or transaction_identity.get("before_fact_sha256")
        != premise_identity.get("fact_sha256")
        or readiness_identity.get("transaction_sha256") != transaction_sha
        or readiness_identity.get("execution_sha256") != execution_sha
        or readiness_identity.get("durable_admission_event_sha256") != event_sha
        or readiness_identity.get("before_frontier_sha256")
        != premise_identity.get("frontier_sha256")
        or readiness_identity.get("after_frontier_sha256")
        != frontier.get("frontier_sha256")
    ):
        raise ExecutionError("episode trigger identity chain is inconsistent")
    apply_module = load_module(
        "apply_for_episode_trigger", APPLY_TRANSACTION_SCRIPT
    )
    if event != apply_module.build_admission_event(transaction):
        raise ExecutionError("episode trigger event does not match its transaction")
    premise_fact = facts.get(premise_id)
    target_fact = facts.get(target_id)
    after_fact = (transaction.get("authoritative_write") or {}).get("after_fact")
    if (
        premise_fact != after_fact
        or digest(premise_fact) != transaction_identity.get("after_fact_sha256")
        or not isinstance(target_fact, dict)
        or premise_id not in target_fact.get("depends_on", [])
    ):
        raise ExecutionError("episode trigger does not establish the target dependency")
    premise_rows = [
        row
        for row in premise_fact.get("evidence", [])
        if isinstance(row.get("checker_operation"), dict)
        and row["checker_operation"].get("id") == premise_operation_id
    ]
    if (
        len(premise_rows) != 1
        or premise_rows[0]["checker_operation"].get("execution_sha256")
        != execution_sha
    ):
        raise ExecutionError("admitted premise does not bind the trigger execution")
    readiness_module = load_module(
        "readiness_for_episode_trigger", READINESS_SCRIPT
    )
    try:
        before_facts, before_registry = readiness_module.repository_inputs_from_execution(
            premise_execution
        )
        expected_readiness = readiness_module.build_authoritative_delta(
            transaction=transaction,
            admission_event=event,
            execution=premise_execution,
            frontier_before=frontier_before,
            frontier_after=frontier,
            before_facts=before_facts,
            facts=facts,
            registry=before_registry,
        )
    except readiness_module.ReadinessError as error:
        raise ExecutionError(f"episode trigger readiness replay failed: {error}") from error
    if readiness != expected_readiness:
        raise ExecutionError("episode trigger readiness is stale or mutated")
    if (
        readiness.get("mode") != "authoritative-ledger"
        or readiness.get("newly_ready") != [target_id]
        or readiness.get("cause")
        != {"event_type": "fact-admitted", "admitted_fact_id": premise_id}
        or readiness.get("authoritative_ledger_writes") != 1
        or readiness.get("fixture_writes") != 0
        or (frontier.get("selection") or {}).get("selected_fact_id") != target_id
    ):
        raise ExecutionError("episode trigger does not uniquely authorize selected A")
    return {
        "premise_fact_id": premise_id,
        "premise_operation_id": premise_operation_id,
        "premise_source_commit": premise_identity["git_commit"],
        "premise_before_fact_sha256": transaction_identity["before_fact_sha256"],
        "premise_after_fact_sha256": transaction_identity["after_fact_sha256"],
        "premise_execution_sha256": execution_sha,
        "premise_transaction_sha256": transaction_sha,
        "premise_admission_event_sha256": event_sha,
        "readiness_delta_sha256": readiness_sha,
        "frontier_after_sha256": frontier["frontier_sha256"],
    }


def episode_state_commit(trigger: dict[str, Any]) -> str:
    """Create a deterministic Git object for the verified post-B/pre-A state.

    The branch, worktree, and real index are untouched. The resulting commit is
    retained by the experiment bundle and gives downstream readiness replay a
    complete ledger pre-state rather than pretending the dirty ledger equals
    its source commit.
    """
    source_commit = trigger.get("premise_source_commit")
    if not isinstance(source_commit, str) or not COMMIT_RE.fullmatch(source_commit):
        raise ExecutionError("episode trigger source commit is invalid")
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    if head != source_commit:
        raise ExecutionError("episode source HEAD differs from the premise execution")
    premise_path = (
        "artifacts/facts/"
        + trigger["premise_fact_id"].replace("F:", "F-")
        + ".json"
    )
    status = subprocess.run(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    changed_paths = [line[3:] for line in status if len(line) >= 4]
    if changed_paths != [premise_path] or status[0][:2] not in {" M", "M ", "MM"}:
        raise ExecutionError(
            "episode state must differ from source HEAD only at the admitted premise"
        )
    with tempfile.TemporaryDirectory(prefix="axeyum-autogenesis-state-index-") as temporary:
        index = pathlib.Path(temporary) / "index"
        environment = dict(os.environ)
        environment.update(
            {
                "GIT_INDEX_FILE": str(index),
                "GIT_AUTHOR_NAME": "axeyum-autogenesis-state",
                "GIT_AUTHOR_EMAIL": "autogenesis-state@invalid",
                "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
                "GIT_COMMITTER_NAME": "axeyum-autogenesis-state",
                "GIT_COMMITTER_EMAIL": "autogenesis-state@invalid",
                "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
            }
        )
        subprocess.run(
            ["git", "read-tree", head], cwd=ROOT, env=environment, check=True
        )
        subprocess.run(
            ["git", "add", "--", premise_path], cwd=ROOT, env=environment, check=True
        )
        tree = subprocess.run(
            ["git", "write-tree"],
            cwd=ROOT,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        commit = subprocess.run(
            ["git", "commit-tree", tree, "-p", head],
            cwd=ROOT,
            env=environment,
            check=True,
            input=(
                "autogenesis-state: admit "
                + trigger["premise_fact_id"]
                + " via "
                + trigger["premise_admission_event_sha256"]
                + "\n"
            ),
            capture_output=True,
            text=True,
        ).stdout.strip()
    if not COMMIT_RE.fullmatch(commit):
        raise ExecutionError("episode state commit identity is invalid")
    changed = subprocess.run(
        ["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    retained = subprocess.run(
        ["git", "show", f"{commit}:{premise_path}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    if changed != [premise_path] or digest(json.loads(retained)) != trigger.get(
        "premise_after_fact_sha256"
    ):
        raise ExecutionError("episode state commit does not contain the verified premise")
    return commit


def parse_kernel_evidence(raw: str) -> dict[str, str]:
    lines = raw.splitlines()
    if not lines or lines[0] != "AXEYUM_AUTOGENESIS_KERNEL_EVIDENCE_V1":
        raise ExecutionError("kernel executor evidence has the wrong kind")
    fields: dict[str, str] = {}
    for line in lines[1:]:
        key, separator, value = line.partition("\t")
        if not separator or not key or key in fields:
            raise ExecutionError("kernel executor evidence fields are malformed")
        fields[key] = value
    required = {
        "candidate",
        "canonical_type",
        "bundle_sha256",
        "catalog_sha256",
        "attempted",
        "budget",
        "accepted_plan_rank",
        "axiom_footprint",
        "retained_answer_dependencies",
    }
    if set(fields) != required:
        raise ExecutionError("kernel executor evidence fields differ from v1")
    return fields


def run_kernel_registered(operation: dict[str, Any]) -> dict[str, Any]:
    executor = operation["executor"]
    frontier_module = load_module("frontier_for_kernel_execution", FRONTIER_SCRIPT)
    fact = frontier_module.load().get(executor["input_fact_id"])
    if not isinstance(fact, dict):
        raise ExecutionError("kernel executor input fact is absent")
    statement = (fact.get("formal") or {}).get("statement")
    if (
        not isinstance(statement, str)
        or not statement.startswith(f"theorem {executor['target_theorem']} : ")
    ):
        raise ExecutionError("kernel executor target theorem differs from formal.statement")
    target_type = formal_type(fact)
    candidate = theorem_candidate(digest(fact), "premise")
    catalog = induction_catalog(fact, candidate, executor["denied_theorems"])
    proposer = load_module("induction_proposer_for_kernel_execution", INDUCTION_PROPOSER)
    try:
        bundle = proposer.build_bundle(catalog)
        projection = proposer.render_tsv(bundle)
    except (KeyError, TypeError, ValueError) as error:
        raise ExecutionError(f"kernel proposal construction failed: {error}") from error
    with tempfile.TemporaryDirectory(prefix="axeyum-authoritative-kernel-") as temporary:
        temporary_root = pathlib.Path(temporary)
        plans = temporary_root / "plans.tsv"
        evidence = temporary_root / "evidence.tsv"
        plans.write_text(projection)
        if os.environ.get("AXEYUM_AUTOGENESIS_INDUCTION_CHECK"):
            raise ExecutionError(
                "authoritative execution forbids the "
                "AXEYUM_AUTOGENESIS_INDUCTION_CHECK override"
            )
        command = [
            "cargo",
            "run",
            "-q",
            "-p",
            "axeyum-lean-kernel",
            "--example",
            "autogenesis_induction_plan_check",
            "--",
        ]
        command.extend(
            [
                "--plans",
                str(plans),
                "--candidate",
                candidate,
                "--budget",
                str(executor["budget"]),
                "--expect",
                "proved",
                "--bundle-sha256",
                bundle["bundle_sha256"],
                "--catalog-sha256",
                catalog["catalog_sha256"],
                "--evidence-output",
                str(evidence),
            ]
        )
        try:
            completed = subprocess.run(
                command,
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=executor["timeout_seconds"],
            )
        except subprocess.TimeoutExpired as error:
            raise ExecutionError("kernel registered operation exceeded its timeout") from error
        if completed.returncode != 0 or not evidence.is_file():
            diagnostic = completed.stderr.strip().splitlines()
            suffix = diagnostic[-1] if diagnostic else "no diagnostic"
            raise ExecutionError(
                f"kernel registered executor exited {completed.returncode}: {suffix}"
            )
        fields = parse_kernel_evidence(evidence.read_text())
    if (
        fields["candidate"] != candidate
        or fields["canonical_type"] != target_type
        or fields["bundle_sha256"] != bundle["bundle_sha256"]
        or fields["catalog_sha256"] != catalog["catalog_sha256"]
        or fields["budget"] != str(executor["budget"])
        or fields["axiom_footprint"] != ""
        or fields["retained_answer_dependencies"] != ""
    ):
        raise ExecutionError("kernel registered evidence differs from the typed request")
    try:
        attempted = int(fields["attempted"])
        accepted_rank = int(fields["accepted_plan_rank"])
    except ValueError as error:
        raise ExecutionError("kernel registered evidence counters are invalid") from error
    return {
        "verdict": "proved",
        "evidence_label": executor["expected_evidence_label"],
        "canonical_type": target_type,
        "axiom_footprint": [],
        "retained_answer_dependencies": [],
        "attempted": attempted,
        "accepted_plan_rank": accepted_rank,
    }


def parse_apply_evidence(raw: str) -> dict[str, str]:
    lines = raw.splitlines()
    if not lines or lines[0] != "AXEYUM_AUTOGENESIS_APPLY_EVIDENCE_V1":
        raise ExecutionError("kernel apply evidence has the wrong kind")
    fields: dict[str, str] = {}
    for line in lines[1:]:
        key, separator, value = line.partition("\t")
        if not separator or not key or key in fields:
            raise ExecutionError("kernel apply evidence fields are malformed")
        fields[key] = value
    required = {
        "candidate",
        "canonical_type",
        "bundle_sha256",
        "catalog_sha256",
        "attempted",
        "budget",
        "accepted_plan_rank",
        "applied_theorem",
        "premise_candidate",
        "premise_attempted",
        "premise_plan_rank",
        "axiom_footprint",
        "retained_answer_dependencies",
    }
    if set(fields) != required:
        raise ExecutionError("kernel apply evidence fields differ from v1")
    return fields


def run_kernel_apply_registered(
    operation: dict[str, Any], trigger: dict[str, Any] | None
) -> dict[str, Any]:
    if trigger is None:
        raise ExecutionError("episode-local apply operation requires a verified B trigger")
    executor = operation["executor"]
    frontier_module = load_module("frontier_for_apply_execution", FRONTIER_SCRIPT)
    facts = frontier_module.load()
    fact = facts.get(executor["input_fact_id"])
    premise_fact = facts.get(executor["premise_fact_id"])
    if not isinstance(fact, dict) or not isinstance(premise_fact, dict):
        raise ExecutionError("apply executor fact or premise is absent")
    statement = (fact.get("formal") or {}).get("statement")
    if (
        not isinstance(statement, str)
        or not statement.startswith(f"theorem {executor['target_theorem']} : ")
    ):
        raise ExecutionError("apply executor target differs from formal.statement")
    if trigger.get("premise_fact_id") != premise_fact["id"]:
        raise ExecutionError("apply trigger names a different premise fact")
    premise_candidate = theorem_candidate(
        trigger["premise_before_fact_sha256"], "premise"
    )
    target_candidate = theorem_candidate(digest(fact), "consequent")
    premise_catalog = induction_catalog(
        premise_fact, premise_candidate, executor["denied_theorems"]
    )
    induction_proposer = load_module(
        "induction_proposer_for_apply_execution", INDUCTION_PROPOSER
    )
    apply_proposer = load_module("apply_proposer_for_execution", APPLY_PROPOSER)
    try:
        premise_bundle = induction_proposer.build_bundle(premise_catalog)
        premise_projection = induction_proposer.render_tsv(premise_bundle)
        apply_catalog: dict[str, Any] = {
            "schema_version": 1,
            "kind": "axeyum-authoritative-kernel-apply-catalog",
            "phase": "post_b",
            "proof_bodies_included": False,
            "denied_theorems": executor["denied_theorems"],
            "trigger": trigger,
            "target": {
                "name": target_candidate,
                "arity": len((fact.get("formal") or {}).get("free_symbols") or []),
                "canonical_type": formal_type(fact),
                "source_fact_id": fact["id"],
            },
            "entries": [
                {
                    "name": premise_candidate,
                    "arity": len(
                        (premise_fact.get("formal") or {}).get("free_symbols") or []
                    ),
                    "canonical_type": formal_type(premise_fact),
                    "origin": "accepted-episode",
                    "source_fact_id": premise_fact["id"],
                }
            ],
        }
        apply_catalog["catalog_sha256"] = digest(apply_catalog)
        apply_bundle = apply_proposer.build_bundle(apply_catalog)
        apply_projection = apply_proposer.render_tsv(apply_bundle)
    except (KeyError, TypeError, ValueError) as error:
        raise ExecutionError(f"kernel apply proposal construction failed: {error}") from error
    if len(apply_bundle["plans"]) != 1:
        raise ExecutionError("exact apply operation did not produce one episode-local plan")
    with tempfile.TemporaryDirectory(prefix="axeyum-authoritative-apply-") as temporary:
        temporary_root = pathlib.Path(temporary)
        premise_plans = temporary_root / "premise-plans.tsv"
        apply_plans = temporary_root / "apply-plans.tsv"
        evidence = temporary_root / "evidence.tsv"
        premise_plans.write_text(premise_projection)
        apply_plans.write_text(apply_projection)
        if os.environ.get("AXEYUM_AUTOGENESIS_APPLY_CHECK"):
            raise ExecutionError(
                "authoritative execution forbids the AXEYUM_AUTOGENESIS_APPLY_CHECK override"
            )
        command = [
            "cargo",
            "run",
            "-q",
            "-p",
            "axeyum-lean-kernel",
            "--example",
            "autogenesis_apply_plan_check",
            "--",
            "--plans",
            str(apply_plans),
            "--phase",
            "post_b",
            "--candidate",
            target_candidate,
            "--premise-candidate",
            premise_candidate,
            "--premise-plans",
            str(premise_plans),
            "--premise-budget",
            str(executor["premise_budget"]),
            "--premise-bundle-sha256",
            premise_bundle["bundle_sha256"],
            "--premise-catalog-sha256",
            premise_catalog["catalog_sha256"],
            "--budget",
            str(executor["budget"]),
            "--expect",
            "proved",
            "--bundle-sha256",
            apply_bundle["bundle_sha256"],
            "--catalog-sha256",
            apply_catalog["catalog_sha256"],
            "--evidence-output",
            str(evidence),
        ]
        try:
            completed = subprocess.run(
                command,
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=executor["timeout_seconds"],
            )
        except subprocess.TimeoutExpired as error:
            raise ExecutionError("kernel apply operation exceeded its timeout") from error
        if completed.returncode != 0 or not evidence.is_file():
            diagnostic = completed.stderr.strip().splitlines()
            suffix = diagnostic[-1] if diagnostic else "no diagnostic"
            raise ExecutionError(
                f"kernel apply executor exited {completed.returncode}: {suffix}"
            )
        fields = parse_apply_evidence(evidence.read_text())
    expected_strings = {
        "candidate": target_candidate,
        "canonical_type": formal_type(fact),
        "bundle_sha256": apply_bundle["bundle_sha256"],
        "catalog_sha256": apply_catalog["catalog_sha256"],
        "budget": str(executor["budget"]),
        "applied_theorem": premise_candidate,
        "premise_candidate": premise_candidate,
        "premise_attempted": str(executor["premise_budget"]),
        "premise_plan_rank": str(executor["premise_budget"]),
        "axiom_footprint": "",
        "retained_answer_dependencies": "",
    }
    if any(fields[key] != value for key, value in expected_strings.items()):
        raise ExecutionError("kernel apply evidence differs from the typed request")
    try:
        attempted = int(fields["attempted"])
        accepted_rank = int(fields["accepted_plan_rank"])
    except ValueError as error:
        raise ExecutionError("kernel apply evidence counters are invalid") from error
    if attempted != executor["budget"] or accepted_rank != executor["budget"]:
        raise ExecutionError("kernel apply evidence did not accept the exact registered plan")
    return {
        "verdict": "proved",
        "evidence_label": executor["expected_evidence_label"],
        "canonical_type": formal_type(fact),
        "axiom_footprint": [],
        "retained_answer_dependencies": [],
        "episode_dependency": premise_candidate,
        "attempted": attempted,
        "accepted_plan_rank": accepted_rank,
        "premise_attempted": executor["premise_budget"],
        "premise_plan_rank": executor["premise_budget"],
    }


def run_registered(
    operation: dict[str, Any], trigger: dict[str, Any] | None = None
) -> dict[str, Any]:
    driver = operation["executor"]["driver"]
    if driver == "axeyum-bench/smtcomp-evidence-v1":
        return run_smt_registered(operation)
    if driver == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        return run_kernel_registered(operation)
    if driver == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        return run_kernel_apply_registered(operation, trigger)
    if driver == "axeyum-lean-import/statement-reflexivity-v1":
        if trigger is not None:
            raise ExecutionError("statement-reflexivity operation rejects a trigger")
        return run_statement_reflexivity_registered(operation)
    raise ExecutionError(f"unsupported execution driver {driver!r}")


def build_receipt(
    *,
    frontier: dict[str, Any],
    fact: dict[str, Any],
    operation: dict[str, Any],
    registry: dict[str, Any],
    git_commit: str,
    observation: dict[str, Any],
    trigger: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if not COMMIT_RE.fullmatch(git_commit):
        raise ExecutionError("execution commit is not a full Git identity")
    executor = operation["executor"]
    if executor["driver"] == "axeyum-bench/smtcomp-evidence-v1":
        expected_observation = {
            "verdict": "unsat",
            "evidence_label": executor["expected_evidence_label"],
            "certified": True,
            "recheck": "na",
            "arena": "ok",
        }
        input_identity = {
            "input_artifact_sha256": byte_digest(
                (ROOT / executor["input_artifact"]).read_bytes()
            )
        }
        request_input = {"input_artifact": executor["input_artifact"]}
    elif executor["driver"] == "axeyum-lean-kernel/nat-zero-add-induction-v1":
        expected_observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "canonical_type": formal_type(fact),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "attempted": executor["budget"],
            "accepted_plan_rank": executor["budget"],
        }
        input_identity = {
            "formal_statement_sha256": byte_digest(
                fact["formal"]["statement"].encode()
            )
        }
        request_input = {
            "target_theorem": executor["target_theorem"],
            "denied_theorems": executor["denied_theorems"],
            "budget": executor["budget"],
        }
    elif executor["driver"] == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        if trigger is None:
            raise ExecutionError("episode-local apply receipt requires its B trigger")
        premise_candidate = theorem_candidate(
            trigger["premise_before_fact_sha256"], "premise"
        )
        expected_observation = {
            "verdict": "proved",
            "evidence_label": executor["expected_evidence_label"],
            "canonical_type": formal_type(fact),
            "axiom_footprint": [],
            "retained_answer_dependencies": [],
            "episode_dependency": premise_candidate,
            "attempted": executor["budget"],
            "accepted_plan_rank": executor["budget"],
            "premise_attempted": executor["premise_budget"],
            "premise_plan_rank": executor["premise_budget"],
        }
        input_identity = {
            "formal_statement_sha256": byte_digest(
                fact["formal"]["statement"].encode()
            ),
            "trigger": trigger,
        }
        request_input = {
            "target_theorem": executor["target_theorem"],
            "premise_fact_id": executor["premise_fact_id"],
            "premise_operation_id": executor["premise_operation_id"],
            "denied_theorems": executor["denied_theorems"],
            "premise_budget": executor["premise_budget"],
            "budget": executor["budget"],
        }
    elif executor["driver"] == "axeyum-lean-import/statement-reflexivity-v1":
        adapter, reflexivity = statement_reflexivity_contract(operation, fact)
        expected_observation = expected_statement_reflexivity_observation(
            operation, fact
        )
        input_identity = {
            "formal_statement_sha256": byte_digest(
                fact["formal"]["statement"].encode()
            ),
            "statement_adapter_manifest_sha256": digest(adapter),
            "reflexivity_manifest_sha256": digest(reflexivity),
            "external_artifact_sha256": adapter["external_artifact"]["sha256"],
        }
        request_input = {
            "statement_adapter_manifest": executor["statement_adapter_manifest"],
            "reflexivity_manifest": executor["reflexivity_manifest"],
            "target_definition": executor["target_definition"],
            "max_binders": executor["max_binders"],
            "max_constructed_nodes": executor["max_constructed_nodes"],
        }
    else:
        raise ExecutionError(f"unsupported execution driver {executor['driver']!r}")
    if observation != expected_observation:
        raise ExecutionError(
            "registered operation observation is not the required source-bound "
            f"result: observed={observation!r}"
        )
    identity_base = {
        "git_commit": git_commit,
        "frontier_sha256": frontier["frontier_sha256"],
        "operation_registry_sha256": digest(registry),
        "fact_id": fact["id"],
        "fact_sha256": digest(fact),
        "operation_id": operation["id"],
        **input_identity,
    }
    identity = dict(identity_base)
    identity["execution_id"] = digest(identity_base)
    receipt: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-operation-execution",
        "identity": identity,
        "request": {
            "driver": executor["driver"],
            "implementation": executor["implementation"],
            "input_fact_id": executor["input_fact_id"],
            **request_input,
            "timeout_seconds": executor["timeout_seconds"],
        },
        "result": {
            "outcome": "proved",
            "epistemic_status": operation["admission"]["epistemic_status"],
            "proof_route": operation["admission"]["proof_route"],
            "evidence_kind": operation["admission"]["evidence_kind"],
            "axiom_footprint_policy": operation["admission"][
                "axiom_footprint_policy"
            ],
            "axiom_footprint": operation["admission"]["axiom_footprint"],
            "observation": observation,
        },
        "acceptance": {
            "source_bound": True,
            "fresh_arena_rechecked": True,
            "caller_authored_command": False,
        },
    }
    receipt["execution_sha256"] = digest(receipt)
    return receipt


def derive(
    frontier_path: pathlib.Path,
    runner: Callable[..., dict[str, Any]] = run_registered,
    trigger_bundle: pathlib.Path | None = None,
) -> dict[str, Any]:
    frontier = json.loads(frontier_path.read_text())
    fact, operation, registry = selected_inputs(frontier)
    driver = operation["executor"]["driver"]
    if driver == "axeyum-lean-kernel/nat-mul-one-episode-apply-v1":
        if trigger_bundle is None:
            raise ExecutionError("selected A operation requires --trigger-bundle")
        frontier_module = load_module("frontier_for_episode_trigger", FRONTIER_SCRIPT)
        trigger = load_episode_trigger(
            bundle=trigger_bundle,
            frontier=frontier,
            facts=frontier_module.load(),
            registry=registry,
            operation=operation,
        )
        commit = episode_state_commit(trigger)
        observation = runner(operation, trigger)
    else:
        if trigger_bundle is not None:
            raise ExecutionError("selected operation does not accept --trigger-bundle")
        trigger = None
        commit = clean_commit()
        observation = runner(operation)
    return build_receipt(
        frontier=frontier,
        fact=fact,
        operation=operation,
        registry=registry,
        git_commit=commit,
        observation=observation,
        trigger=trigger,
    )


def verify_receipt(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    claimed = actual.get("execution_sha256")
    unsigned = dict(actual)
    unsigned.pop("execution_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise ExecutionError("execution receipt digest is missing or invalid")
    if actual != expected:
        raise ExecutionError("execution receipt is stale or mutated")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier", required=True, type=pathlib.Path)
    parser.add_argument("--trigger-bundle", type=pathlib.Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--output", type=pathlib.Path)
    action.add_argument("--verify", type=pathlib.Path)
    args = parser.parse_args()
    try:
        expected = derive(
            args.frontier.resolve(),
            trigger_bundle=(
                args.trigger_bundle.resolve() if args.trigger_bundle is not None else None
            ),
        )
        if args.verify is not None:
            verify_receipt(json.loads(args.verify.read_text()), expected)
            print(f"AUTOGENESIS_OPERATION_EXECUTION_OK|{expected['execution_sha256']}")
        else:
            output = args.output.resolve()
            if output.exists():
                raise ExecutionError(f"refusing to overwrite {output}")
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
            print(
                f"AUTOGENESIS_OPERATION_EXECUTION|{expected['execution_sha256']}|"
                f"fact={expected['identity']['fact_id']}|"
                f"operation={expected['identity']['operation_id']}|{output}"
            )
        return 0
    except (
        OSError,
        subprocess.SubprocessError,
        json.JSONDecodeError,
        KeyError,
        TypeError,
        ExecutionError,
    ) as error:
        print(f"AUTOGENESIS_OPERATION_EXECUTION_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
