#!/usr/bin/env python3
"""Run and retain one machine-selected authoritative fact admission.

The caller chooses only an output directory. The current machine frontier
chooses the fact, the operation registry chooses the producer/checker, and the
transaction chooses the ledger delta. The runner deliberately injects a crash
after durable intent, proves the fact is unchanged, recovers exactly once, and
retains every receipt needed to audit the write.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"


class AdmissionRunError(RuntimeError):
    """The authoritative run cannot continue without weakening a guard."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def file_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise AdmissionRunError(f"expected JSON object: {path}")
    return value


def write(path: pathlib.Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run(
    arguments: list[str],
    *,
    cwd: pathlib.Path = ROOT,
    expected: int = 0,
) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        arguments,
        cwd=cwd,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != expected:
        raise AdmissionRunError(
            f"command exited {completed.returncode}, expected {expected}: "
            f"{' '.join(arguments)}\nstdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        )
    return completed


def git(*arguments: str) -> str:
    return run(["git", *arguments]).stdout.strip()


def require_clean() -> None:
    status = git("status", "--porcelain", "--untracked-files=all")
    if status:
        raise AdmissionRunError("source checkout must be clean")


def changed_paths() -> list[str]:
    lines = git("status", "--porcelain", "--untracked-files=all").splitlines()
    if any(len(line) < 4 or line[:2] not in {" M", "M ", "??"} for line in lines):
        raise AdmissionRunError(f"unsupported worktree state: {lines}")
    return sorted(line[3:] for line in lines)


def selected_fact_path(frontier: dict[str, Any]) -> tuple[str, pathlib.Path]:
    selection = frontier.get("selection")
    if not isinstance(selection, dict):
        raise AdmissionRunError("frontier selection is absent")
    fact_id = selection.get("selected_fact_id")
    admissible = selection.get("admissible_fact_ids")
    if (
        not isinstance(fact_id, str)
        or not fact_id.startswith("F:")
        or not isinstance(admissible, list)
        or fact_id not in admissible
    ):
        raise AdmissionRunError("frontier has no exact admissible selected fact")
    path = FACTS / (fact_id.replace("F:", "F-") + ".json")
    if not path.is_file() or load(path).get("id") != fact_id:
        raise AdmissionRunError("selected fact does not resolve to one canonical ledger file")
    return fact_id, path


def artifact_digests(root: pathlib.Path) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): file_digest(path)
        for path in sorted(root.rglob("*"))
        if path.is_file() and path.name != "run.json"
    }


def execute(output: pathlib.Path) -> dict[str, Any]:
    source_root = ROOT.resolve()
    output = output.resolve()
    if output == source_root or source_root in output.parents:
        raise AdmissionRunError("retained output must be outside the source checkout")
    if output.exists():
        raise AdmissionRunError("refusing to overwrite retained output")
    require_clean()
    source_commit = git("rev-parse", "HEAD")

    # The journal and fact must share a filesystem for atomic replacement.
    # Keep a failed run rather than deleting its only recovery material.
    scratch = pathlib.Path(
        tempfile.mkdtemp(prefix="axeyum-authoritative-fact.", dir=source_root.parent)
    )
    stage = scratch / "retained"
    journal = scratch / "journal"
    stage.mkdir()
    journal.mkdir()
    success = False
    try:
        run(
            [
                "python3",
                "scripts/fact-frontier.py",
                "--output",
                str(stage / "frontier-before.json"),
            ]
        )
        frontier_before = load(stage / "frontier-before.json")
        fact_id, fact_path = selected_fact_path(frontier_before)
        relative_fact = fact_path.relative_to(ROOT)
        shutil.copy2(fact_path, stage / "before-fact.json")

        run(
            [
                "python3",
                "scripts/execute-autogenesis-operation.py",
                "--frontier",
                str(stage / "frontier-before.json"),
                "--output",
                str(stage / "execution.json"),
            ]
        )
        run(
            [
                "python3",
                "scripts/execute-autogenesis-operation.py",
                "--frontier",
                str(stage / "frontier-before.json"),
                "--verify",
                str(stage / "execution.json"),
            ]
        )
        execution = load(stage / "execution.json")
        if execution.get("identity", {}).get("git_commit") != source_commit:
            raise AdmissionRunError("execution is not bound to the clean source commit")

        transaction_base = [
            "python3",
            "scripts/prepare-autogenesis-fact-transaction.py",
            "--fact",
            str(relative_fact),
            "--frontier",
            str(stage / "frontier-before.json"),
            "--execution",
            str(stage / "execution.json"),
        ]
        run([*transaction_base, "--output", str(stage / "transaction.json")])
        run([*transaction_base, "--verify", str(stage / "transaction.json")])
        transaction = load(stage / "transaction.json")

        apply_base = [
            "python3",
            "scripts/apply-autogenesis-fact-transaction.py",
            "--transaction",
            str(stage / "transaction.json"),
            "--frontier",
            str(stage / "frontier-before.json"),
            "--execution",
            str(stage / "execution.json"),
            "--before-fact",
            str(relative_fact),
            "--journal-dir",
            str(journal),
        ]
        run([*apply_base, "--fault-after", "intent"], expected=75)
        if fact_path.read_bytes() != (stage / "before-fact.json").read_bytes():
            raise AdmissionRunError("intent-boundary fault changed the authoritative fact")
        run(
            [
                "python3",
                "scripts/apply-autogenesis-fact-transaction.py",
                "--transaction",
                str(stage / "transaction.json"),
                "--journal-dir",
                str(journal),
                "--recover",
            ]
        )

        transaction_sha = transaction["transaction_sha256"]
        journal_stage = journal / transaction_sha
        for name in ("intent.json", "admission-event.json"):
            shutil.copy2(journal_stage / name, stage / name)
        shutil.copy2(fact_path, stage / "after-fact.json")
        if file_digest(fact_path) != transaction["identity"]["after_fact_sha256"]:
            raise AdmissionRunError("recovered fact differs from the transaction delta")

        run(
            [
                "python3",
                "scripts/fact-frontier.py",
                "--output",
                str(stage / "frontier-after.json"),
            ]
        )
        readiness_base = [
            "python3",
            "scripts/create-autogenesis-readiness-delta.py",
            "--transaction",
            str(stage / "transaction.json"),
            "--durable-admission-event",
            str(stage / "admission-event.json"),
            "--execution",
            str(stage / "execution.json"),
            "--frontier-before",
            str(stage / "frontier-before.json"),
            "--frontier-after",
            str(stage / "frontier-after.json"),
        ]
        run([*readiness_base, "--output", str(stage / "readiness.json")])
        run([*readiness_base, "--verify", str(stage / "readiness.json")])
        readiness = load(stage / "readiness.json")
        if (
            readiness.get("authoritative_ledger_writes") != 1
            or readiness.get("frontier_change", {}).get("selected_before") != fact_id
        ):
            raise AdmissionRunError("readiness receipt does not describe one selected write")

        run(
            [
                "python3",
                "scripts/check-autogenesis-fact-operation.py",
                "--fact",
                str(relative_fact),
            ]
        )
        run(["python3", "scripts/validate-facts.py"])
        if changed_paths() != [relative_fact.as_posix()]:
            raise AdmissionRunError("authoritative run changed a path other than its selected fact")
        run(["git", "diff", "--check", "--", relative_fact.as_posix()])

        report: dict[str, Any] = {
            "schema_version": 1,
            "kind": "axeyum-autogenesis-authoritative-fact-run",
            "source_commit": source_commit,
            "fact_id": fact_id,
            "fact_path": relative_fact.as_posix(),
            "operation_id": execution["identity"]["operation_id"],
            "frontier_before_sha256": frontier_before["frontier_sha256"],
            "execution_sha256": execution["execution_sha256"],
            "transaction_sha256": transaction_sha,
            "admission_event_sha256": load(stage / "admission-event.json")[
                "event_sha256"
            ],
            "readiness_sha256": readiness["readiness_sha256"],
            "fault": {
                "boundary": "after-intent",
                "exit_status": 75,
                "fact_unchanged_before_recovery": True,
            },
            "result": {
                "recovery_executions": 1,
                "authoritative_ledger_writes": 1,
                "fact_operation_checker_passed": True,
                "axiom_footprint": execution["result"]["axiom_footprint"],
                "retained_answer_dependencies": execution["result"]["observation"][
                    "retained_answer_dependencies"
                ],
                "selected_after": readiness["frontier_change"]["selected_after"],
            },
            "artifacts": artifact_digests(stage),
        }
        report["run_sha256"] = digest(report)
        write(stage / "run.json", report)
        shutil.copytree(stage, output)
        success = True
        return report
    finally:
        if success:
            shutil.rmtree(scratch)
        else:
            print(
                f"AUTOGENESIS_AUTHORITATIVE_FACT_RECOVERY_REQUIRED|scratch={scratch}",
                flush=True,
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=pathlib.Path)
    args = parser.parse_args()
    report = execute(args.output)
    print(
        f"AUTOGENESIS_AUTHORITATIVE_FACT_OK|{report['run_sha256']}|"
        f"fact={report['fact_id']}|operation={report['operation_id']}|"
        f"output={args.output.resolve()}"
    )


if __name__ == "__main__":
    try:
        main()
    except (AdmissionRunError, OSError, KeyError, TypeError, ValueError) as error:
        print(f"AUTOGENESIS_AUTHORITATIVE_FACT_ERROR|{error}", file=sys.stderr)
        raise SystemExit(1)
