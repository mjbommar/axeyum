#!/usr/bin/env python3
"""Run the credited Autogenesis B -> A acquisition in an isolated worktree.

This is intentionally an orchestration script, not another proof authority.  It
composes the registered frontier, executor, transaction, recovery, readiness,
and fact-operation checkers and retains every input needed to audit the run.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parent.parent
B_ID = "F:nat-zero-add"
A_ID = "F:nat-mul-one"
B_PATH = pathlib.Path("artifacts/facts/F-nat-zero-add.json")
A_PATH = pathlib.Path("artifacts/facts/F-nat-mul-one.json")
B_OPERATION = "authoritative-kernel-nat-zero-add-induction-v1"
A_OPERATION = "authoritative-kernel-nat-mul-one-episode-apply-v1"
PRIOR_ART = {
    B_ID: "zero is a left identity for natural-number addition",
    A_ID: "one is a right identity for natural-number multiplication",
}


class ChainError(RuntimeError):
    """The chain cannot continue without guessing or weakening a gate."""


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def file_digest(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ChainError(f"expected JSON object: {path}")
    return value


def write(path: pathlib.Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run(
    arguments: list[str],
    *,
    cwd: pathlib.Path,
    env: dict[str, str] | None = None,
    expected: int = 0,
    quiet: bool = True,
) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        arguments,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE if quiet else None,
        stderr=subprocess.PIPE if quiet else None,
        check=False,
    )
    if completed.returncode != expected:
        detail = ""
        if quiet:
            detail = f"\nstdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        raise ChainError(
            f"command exited {completed.returncode}, expected {expected}: "
            f"{' '.join(arguments)}{detail}"
        )
    return completed


def git(cwd: pathlib.Path, *arguments: str) -> str:
    return run(["git", *arguments], cwd=cwd).stdout.strip()


def require_clean(cwd: pathlib.Path, label: str) -> None:
    status = run(
        ["git", "status", "--porcelain", "--untracked-files=all"], cwd=cwd
    ).stdout.rstrip("\n")
    if status:
        raise ChainError(f"{label} must be clean")


def changed_paths(cwd: pathlib.Path) -> list[str]:
    lines = run(
        ["git", "status", "--porcelain", "--untracked-files=all"], cwd=cwd
    ).stdout.splitlines()
    if any(len(line) < 4 or line[:2] not in {" M", "M ", "??"} for line in lines):
        raise ChainError(f"unsupported worktree state: {lines}")
    return sorted(line[3:] for line in lines)


def make_open_prestate(checkout: pathlib.Path) -> None:
    for fact_id, relative in ((B_ID, B_PATH), (A_ID, A_PATH)):
        path = checkout / relative
        fact = load(path)
        if fact.get("id") != fact_id or fact.get("epistemic_status") != "proved":
            raise ChainError(f"credited prestate requires settled source fact {fact_id}")
        fact["epistemic_status"] = "open"
        fact["evidence"] = []
        fact.pop("proof_route", None)
        fact.pop("axiom_footprint", None)
        provenance = fact.get("provenance")
        if not isinstance(provenance, dict):
            raise ChainError(f"{fact_id} has no provenance object")
        provenance["prior_art"] = [
            {
                "who": "standard Peano arithmetic",
                "what": PRIOR_ART[fact_id],
                "attribution": (
                    "synthetic open-state reconstruction; no external-source "
                    "credit is claimed"
                ),
            }
        ]
        write(path, fact)


def command_env(scratch: pathlib.Path) -> dict[str, str]:
    env = dict(os.environ)
    env.setdefault("CARGO_TARGET_DIR", str(scratch / "target"))
    return env


def execute_stage(
    *,
    checkout: pathlib.Path,
    stage: pathlib.Path,
    fact_path: pathlib.Path,
    journal: pathlib.Path,
    env: dict[str, str],
    trigger: pathlib.Path | None,
) -> None:
    stage.mkdir(parents=True)
    shutil.copy2(checkout / fact_path, stage / "before-fact.json")
    run(
        ["python3", "scripts/fact-frontier.py", "--output", str(stage / "frontier-before.json")],
        cwd=checkout,
    )
    trigger_args = [] if trigger is None else ["--trigger-bundle", str(trigger)]
    run(
        [
            "python3",
            "scripts/execute-autogenesis-operation.py",
            "--frontier",
            str(stage / "frontier-before.json"),
            *trigger_args,
            "--output",
            str(stage / "execution.json"),
        ],
        cwd=checkout,
        env=env,
    )
    run(
        [
            "python3",
            "scripts/execute-autogenesis-operation.py",
            "--frontier",
            str(stage / "frontier-before.json"),
            *trigger_args,
            "--verify",
            str(stage / "execution.json"),
        ],
        cwd=checkout,
        env=env,
    )
    run(
        [
            "python3",
            "scripts/prepare-autogenesis-fact-transaction.py",
            "--fact",
            str(fact_path),
            "--frontier",
            str(stage / "frontier-before.json"),
            "--execution",
            str(stage / "execution.json"),
            *trigger_args,
            "--output",
            str(stage / "transaction.json"),
        ],
        cwd=checkout,
        env=env,
    )
    run(
        [
            "python3",
            "scripts/prepare-autogenesis-fact-transaction.py",
            "--fact",
            str(fact_path),
            "--frontier",
            str(stage / "frontier-before.json"),
            "--execution",
            str(stage / "execution.json"),
            *trigger_args,
            "--verify",
            str(stage / "transaction.json"),
        ],
        cwd=checkout,
        env=env,
    )

    run(
        [
            "python3",
            "scripts/apply-autogenesis-fact-transaction.py",
            "--transaction",
            str(stage / "transaction.json"),
            "--frontier",
            str(stage / "frontier-before.json"),
            "--execution",
            str(stage / "execution.json"),
            *trigger_args,
            "--before-fact",
            str(fact_path),
            "--journal-dir",
            str(journal),
            "--fault-after",
            "intent",
        ],
        cwd=checkout,
        env=env,
        expected=75,
    )
    if (checkout / fact_path).read_bytes() != (stage / "before-fact.json").read_bytes():
        raise ChainError("intent-boundary fault changed the authoritative fact")
    run(
        [
            "python3",
            "scripts/apply-autogenesis-fact-transaction.py",
            "--transaction",
            str(stage / "transaction.json"),
            "--journal-dir",
            str(journal),
            "--recover",
        ],
        cwd=checkout,
        env=env,
    )
    transaction = load(stage / "transaction.json")
    transaction_sha = transaction["transaction_sha256"]
    journal_stage = stage / "journal" / transaction_sha
    journal_stage.mkdir(parents=True)
    for name in ("intent.json", "admission-event.json"):
        shutil.copy2(journal / transaction_sha / name, journal_stage / name)
    shutil.copy2(journal_stage / "admission-event.json", stage / "admission-event.json")
    shutil.copy2(checkout / fact_path, stage / "after-fact.json")
    run(
        ["python3", "scripts/fact-frontier.py", "--output", str(stage / "frontier-after.json")],
        cwd=checkout,
    )
    readiness = [
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
    run([*readiness, "--output", str(stage / "readiness.json")], cwd=checkout)
    run([*readiness, "--verify", str(stage / "readiness.json")], cwd=checkout)


def semantic_checks(fresh: pathlib.Path, source_head: str, prestate: str) -> dict[str, bool]:
    negative = load(fresh / "pre-b-negative" / "experiment.json")
    b_frontier = load(fresh / "b" / "frontier-before.json")
    b_execution = load(fresh / "b" / "execution.json")
    b_readiness = load(fresh / "b" / "readiness.json")
    a_frontier = load(fresh / "a" / "frontier-before.json")
    a_frontier_after = load(fresh / "a" / "frontier-after.json")
    a_execution = load(fresh / "a" / "execution.json")
    a_readiness = load(fresh / "a" / "readiness.json")
    return {
        "source_commit_bound": negative.get("git_commit") == source_head,
        "same_pre_b_a_target": negative.get("same_target") is True,
        "same_pre_b_a_budget": negative.get("budget") == a_execution["request"]["budget"],
        "pre_b_a_exhausted_budget_without_proof": "outcome=no-proof" in negative["pre_a"]["result"],
        "b_selected": b_frontier["selection"]["selected_fact_id"] == B_ID,
        "b_registered_operation": b_execution["identity"]["operation_id"] == B_OPERATION,
        "b_source_is_prestate": b_execution["identity"]["git_commit"] == prestate,
        "b_proved_axiom_free": b_execution["result"]["axiom_footprint"] == [],
        "b_no_retained_answer": b_execution["result"]["observation"]["retained_answer_dependencies"] == [],
        "b_one_authoritative_write": b_readiness["authoritative_ledger_writes"] == 1,
        "b_zero_fixture_writes": b_readiness["fixture_writes"] == 0,
        "b_unlocks_exactly_a": b_readiness["newly_ready"] == [A_ID],
        "a_selected_after_b": a_frontier["selection"]["selected_fact_id"] == A_ID,
        "a_registered_operation": a_execution["identity"]["operation_id"] == A_OPERATION,
        "a_trigger_names_b": a_execution["identity"]["trigger"]["premise_fact_id"] == B_ID,
        "a_uses_episode_local_b": a_execution["result"]["observation"]["episode_dependency"].startswith(
            "Autogenesis.Authoritative.E"
        ),
        "a_proved_axiom_free": a_execution["result"]["axiom_footprint"] == [],
        "a_no_retained_answer": a_execution["result"]["observation"]["retained_answer_dependencies"] == [],
        "a_one_authoritative_write": a_readiness["authoritative_ledger_writes"] == 1,
        "a_zero_fixture_writes": a_readiness["fixture_writes"] == 0,
        "a_removed_from_ready": a_readiness["frontier_change"]["no_longer_ready"] == [A_ID],
        "final_frontier_has_no_registered_candidate": (
            a_frontier_after["selection"]["outcome"] == "refused-no-admissible-candidate"
            and a_frontier_after["selection"]["selected_fact_id"] is None
        ),
    }


def artifact_digests(root: pathlib.Path) -> dict[str, str]:
    return {
        str(path.relative_to(root)): file_digest(path)
        for path in sorted(root.rglob("*"))
        if path.is_file() and path.name != "run.json"
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run and retain one clean authoritative Autogenesis B -> A chain."
    )
    parser.add_argument("output", type=pathlib.Path)
    args = parser.parse_args()

    output = args.output.resolve()
    source_root = ROOT.resolve()
    if output == source_root or source_root in output.parents:
        raise ChainError("retained output must be outside the source checkout")
    if output.exists():
        raise ChainError("refusing to overwrite retained output")
    require_clean(source_root, "source checkout")
    source_head = git(source_root, "rev-parse", "HEAD")

    with tempfile.TemporaryDirectory(prefix="axeyum-authoritative-chain.", dir="/tmp") as raw:
        scratch = pathlib.Path(raw)
        checkout = scratch / "checkout"
        fresh = scratch / "fresh"
        fresh.mkdir()
        env = command_env(scratch)
        ref = f"refs/autogenesis-experiments/authoritative-chain-{source_head}"
        ref_created = False
        worktree_created = False
        try:
            print("AUTOGENESIS_CHAIN_PHASE|pre-b-negative-control", flush=True)
            run(
                [
                    "scripts/check-autogenesis-apply-search.sh",
                    "--retain",
                    str(fresh / "pre-b-negative"),
                ],
                cwd=source_root,
                env=env,
            )
            run(["git", "worktree", "add", "--detach", str(checkout), source_head], cwd=source_root)
            worktree_created = True
            make_open_prestate(checkout)
            run(["git", "add", str(B_PATH), str(A_PATH)], cwd=checkout)
            commit_env = dict(env)
            commit_env.update(
                {
                    "GIT_AUTHOR_NAME": "axeyum-autogenesis-replay",
                    "GIT_AUTHOR_EMAIL": "autogenesis-replay@invalid",
                    "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
                    "GIT_COMMITTER_NAME": "axeyum-autogenesis-replay",
                    "GIT_COMMITTER_EMAIL": "autogenesis-replay@invalid",
                    "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
                }
            )
            run(
                ["git", "commit", "--no-verify", "-m", "test(autogenesis): reconstruct B and A open pre-state"],
                cwd=checkout,
                env=commit_env,
            )
            prestate = git(checkout, "rev-parse", "HEAD")
            require_clean(checkout, "reconstructed prestate")
            run(["python3", "scripts/validate-facts.py"], cwd=checkout)

            print("AUTOGENESIS_CHAIN_PHASE|admit-b", flush=True)
            shutil.copy2(checkout / A_PATH, fresh / "b-before-consequent-fact.json")
            execute_stage(
                checkout=checkout,
                stage=fresh / "b",
                fact_path=B_PATH,
                journal=scratch / "journal-b",
                env=env,
                trigger=None,
            )
            observed_b_paths = changed_paths(checkout)
            if observed_b_paths != [str(B_PATH)]:
                raise ChainError(
                    "B admission changed paths other than the B fact: "
                    f"{observed_b_paths}"
                )

            print("AUTOGENESIS_CHAIN_PHASE|admit-a", flush=True)
            execute_stage(
                checkout=checkout,
                stage=fresh / "a",
                fact_path=A_PATH,
                journal=scratch / "journal-a",
                env=env,
                trigger=fresh / "b",
            )
            observed_chain_paths = changed_paths(checkout)
            if observed_chain_paths != sorted((str(A_PATH), str(B_PATH))):
                raise ChainError(
                    "two-write run changed paths outside B and A: "
                    f"{observed_chain_paths}"
                )
            for fact_path in (B_PATH, A_PATH):
                run(
                    ["python3", "scripts/check-autogenesis-fact-operation.py", "--fact", str(fact_path)],
                    cwd=checkout,
                    env=env,
                )
            run(["python3", "scripts/validate-facts.py"], cwd=checkout)

            a_execution = load(fresh / "a" / "execution.json")
            state_commit = a_execution["identity"]["git_commit"]
            if subprocess.run(
                ["git", "show-ref", "--verify", "--quiet", ref],
                cwd=source_root,
                check=False,
            ).returncode == 0:
                raise ChainError(f"temporary retention ref already exists: {ref}")
            run(["git", "update-ref", ref, state_commit, "0" * 40], cwd=source_root)
            ref_created = True
            bundle = fresh / "pre-a-state.bundle"
            run(["git", "bundle", "create", str(bundle), ref, f"^{source_head}"], cwd=source_root)
            run(["git", "bundle", "verify", str(bundle)], cwd=source_root)

            checks = semantic_checks(fresh, source_head, prestate)
            if not all(checks.values()):
                failed = sorted(name for name, passed in checks.items() if not passed)
                raise ChainError(f"semantic chain checks failed: {failed}")
            report: dict[str, Any] = {
                "schema_version": 1,
                "kind": "axeyum-autogenesis-authoritative-two-write-run",
                "source_commit": source_head,
                "reconstructed_prestate_commit": prestate,
                "pre_a_state_commit": state_commit,
                "bundle": {
                    "path": "pre-a-state.bundle",
                    "prerequisite_commit": source_head,
                    "state_ref": ref,
                    "sha256": file_digest(bundle),
                },
                "chain": {"premise": B_ID, "consequent": A_ID},
                "budgets": {"pre_b_a_negative": 1, "b": 2, "a": 1},
                "intervention_audit": {
                    "human_written_or_repaired_proofs": 0,
                    "human_interventions_after_launch": 0,
                    "caller_authored_checker_commands": 0,
                },
                "trusted_base_audit": {
                    "source_changes_during_run": [],
                    "trusted_base_files_changed": [],
                    "b_axiom_footprint": [],
                    "a_axiom_footprint": [],
                },
                "fault_injection": {
                    "b": {"boundary": "after-intent", "exit_status": 75, "recovered": True},
                    "a": {"boundary": "after-intent", "exit_status": 75, "recovered": True},
                },
                "checks": checks,
                "artifacts": artifact_digests(fresh),
            }
            report["run_sha256"] = canonical_digest(report)
            write(fresh / "run.json", report)
            shutil.copytree(fresh, output)
            require_clean(source_root, "source checkout after chain")
            print(
                f"AUTOGENESIS_AUTHORITATIVE_CHAIN_OK|{report['run_sha256']}|"
                f"source={source_head}|output={output}",
                flush=True,
            )
        finally:
            if ref_created:
                subprocess.run(
                    ["git", "update-ref", "-d", ref], cwd=source_root, check=False
                )
            if worktree_created:
                subprocess.run(
                    ["git", "worktree", "remove", "--force", str(checkout)],
                    cwd=source_root,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    check=False,
                )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ChainError, OSError, KeyError, TypeError, ValueError) as error:
        print(f"AUTOGENESIS_AUTHORITATIVE_CHAIN_ERROR|{error}", file=sys.stderr)
        raise SystemExit(1)
