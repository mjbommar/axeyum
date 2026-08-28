#!/usr/bin/env python3
"""Independently re-derive and check the ten `Nat.ModEq` congruence targets.

`authoritative-mathlib-nat-modeq-congruence-family-v1` closes ten of the
eleven `natural-modular-equivalence` propositions that were `open` on
2026-08-28, through `producers::conclusion_directed_application` and the
`conclusion_directed_transport_probe` checker, against hash-pinned
statement-only Mathlib exports and one tracked, axiom-free Lean candidate
contract.

WHAT THIS SCRIPT IS FOR. A checker that cannot fail is worse than no checker,
so nothing here reports completion. Every field of every replayed receipt is
compared against the committed manifest exactly; a changed proof, a changed
goal, a changed export, a lost axiom-freedom, a newly-cited theorem
dependency, or a target self-citation each fail loudly and separately. The
script also confirms the checker DECLINES on a nonexistent input path, so a
run that silently checked nothing cannot pass.

WHAT IT DOES NOT CLAIM. Each admitted target proof cites exactly one imported
candidate theorem, named in the manifest, whose own proof is authored in the
tracked contract source and re-checked by this kernel. That is ADR-0601's
"producer behind one trust anchor", not a Mathlib proof import: no Mathlib
proof value for any target was exposed, and `target_dependency` is false on
every row. The script asserts both of those from the probe's own mechanical
audit over `Kernel::declaration_dependency_closure`, never from this comment.

LEDGER CONSISTENCY IS CHECKED BOTH WAYS. A fact this operation names must be
`proved` with an evidence row bound to the operation id and carrying the same
`goal_sha256`/`proof_sha256` this run re-derives; a fact that is still `open`
while the manifest claims it converted is equally a failure. An operation
whose facts drifted to `proved` without a matching evidence row is exactly the
defect this ledger tracks.

Exit 0 only when every target replays identically. Exit 1 on any mismatch,
exit 2 on a setup or manifest error — deliberately distinct.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "artifacts/autogenesis/nat-modeq-congruence-contract-v1.json"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
FACTS = ROOT / "artifacts/facts"
OPERATION_ID = "authoritative-mathlib-nat-modeq-congruence-family-v1"
PROBE = "conclusion_directed_transport_probe"
CANDIDATE_STREAM = (
    "/nas3/data/axeyum/autogenesis/reference-packs/"
    "nat-modeq-congruence-v1/candidates.ndjson"
)


class CheckError(Exception):
    """A setup problem: the subject could not be examined at all."""


def sha256_file(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_manifest() -> dict:
    if not MANIFEST.is_file():
        raise CheckError(f"missing manifest {MANIFEST.relative_to(ROOT)}")
    try:
        manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckError(f"unreadable manifest: {exc}") from exc
    outcomes = manifest.get("outcomes")
    if not isinstance(outcomes, list) or not outcomes:
        raise CheckError("manifest carries no outcomes — the check has no subject")
    return manifest


def build_probe() -> pathlib.Path:
    binary = ROOT / "target/release/examples" / PROBE
    command = [
        "cargo",
        "build",
        "--release",
        "-p",
        "axeyum-lean-import",
        "--example",
        PROBE,
    ]
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if result.returncode != 0:
        raise CheckError(f"cannot build {PROBE}: {result.stderr[-2000:]}")
    if not binary.is_file():
        raise CheckError(f"{PROBE} did not produce {binary}")
    return binary


def run_probe(binary: pathlib.Path, target_stream: str, target: str, roots: list[str]):
    command = [str(binary), target_stream, target, CANDIDATE_STREAM, *roots]
    return subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=600)


def parse_probe_line(text: str) -> dict[str, str]:
    for line in text.splitlines():
        if line.startswith("CONCLUSION_DIRECTED_TRANSPORT|result=accepted|"):
            fields: dict[str, str] = {}
            for part in line.split("|")[1:]:
                key, _, value = part.partition("=")
                fields[key] = value
            return fields
    raise CheckError("probe printed no accepted receipt line")


def check_external_inputs(manifest: dict, failures: list[str]) -> None:
    inputs = manifest.get("external_inputs")
    if not isinstance(inputs, list) or not inputs:
        raise CheckError("manifest carries no external_inputs")
    for entry in inputs:
        path = pathlib.Path(entry["path"])
        if not path.is_file():
            failures.append(f"external input missing: {path}")
            continue
        actual_mode = format(os.stat(path).st_mode & 0o7777, "04o")
        if actual_mode != entry["mode"]:
            failures.append(
                f"{path.name}: mode {actual_mode} != pinned {entry['mode']}"
            )
        actual_size = path.stat().st_size
        if actual_size != entry["bytes"]:
            failures.append(
                f"{path.name}: {actual_size} bytes != pinned {entry['bytes']}"
            )
        actual_sha = sha256_file(path)
        if actual_sha != entry["sha256"]:
            failures.append(f"{path.name}: sha256 {actual_sha} != pinned")


def check_tracked_sources(manifest: dict, failures: list[str]) -> None:
    for key in ("contract_source", "statement_adapter_source"):
        entry = manifest.get(key)
        if not isinstance(entry, dict):
            failures.append(f"manifest has no {key}")
            continue
        path = ROOT / entry["path"]
        if not path.is_file():
            failures.append(f"{key} missing: {entry['path']}")
            continue
        actual = sha256_file(path)
        if actual != entry["sha256"]:
            failures.append(f"{entry['path']}: sha256 {actual} != pinned")


def check_ledger(manifest: dict, failures: list[str]) -> None:
    try:
        registry = json.loads(OPERATIONS.read_text(encoding="utf-8"))["operations"]
    except (OSError, KeyError, json.JSONDecodeError) as exc:
        raise CheckError(f"unreadable operations registry: {exc}") from exc
    operation = next((o for o in registry if o.get("id") == OPERATION_ID), None)
    if operation is None:
        failures.append(f"operation {OPERATION_ID} is not registered")
        return
    named = set(operation.get("applicability", {}).get("fact_ids", []))
    converted = {o["fact_id"] for o in manifest["outcomes"]}
    missing = converted - named
    if missing:
        failures.append(
            f"{OPERATION_ID} does not name converted fact(s) {sorted(missing)}"
        )
    for outcome in manifest["outcomes"]:
        fact_id = outcome["fact_id"]
        path = FACTS / (fact_id.replace("F:", "F-") + ".json")
        if not path.is_file():
            failures.append(f"fact file missing for {fact_id}")
            continue
        fact = json.loads(path.read_text(encoding="utf-8"))
        if fact.get("epistemic_status") != "proved":
            failures.append(
                f"{fact_id}: manifest says converted, ledger says "
                f"{fact.get('epistemic_status')!r}"
            )
            continue
        rows = [
            row
            for row in fact.get("evidence", [])
            if (row.get("checker_operation") or {}).get("id") == OPERATION_ID
        ]
        if not rows:
            failures.append(f"{fact_id}: proved with no evidence row for {OPERATION_ID}")
            continue
        row = rows[0]["checker_operation"]
        for field in ("goal_sha256", "proof_sha256", "target_content_sha256"):
            if row.get(field) != outcome[field]:
                failures.append(
                    f"{fact_id}: evidence {field} disagrees with the manifest"
                )
        if fact.get("axiom_footprint") != []:
            failures.append(f"{fact_id}: axiom_footprint is not empty")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    manifest = load_manifest()
    roots = manifest["contract_source"]["candidate_roots"]
    failures: list[str] = []

    check_external_inputs(manifest, failures)
    check_tracked_sources(manifest, failures)

    binary = build_probe()

    # The checker must DECLINE on an input that does not exist. Without this a
    # broken probe that always exits 0 would replay ten targets "successfully".
    absent = run_probe(binary, "/nonexistent/nat-modeq-congruence-absent.ndjson", "X", roots)
    if absent.returncode == 0:
        failures.append(
            "probe accepted a nonexistent target stream — it cannot fail, so its "
            "ten passes prove nothing"
        )

    replayed = 0
    for outcome in manifest["outcomes"]:
        result = run_probe(
            binary, outcome["target_stream"], outcome["target_definition"], roots
        )
        if result.returncode != 0:
            failures.append(
                f"{outcome['fact_id']}: probe declined: {result.stderr.strip()[:400]}"
            )
            continue
        try:
            fields = parse_probe_line(result.stdout)
        except CheckError as exc:
            failures.append(f"{outcome['fact_id']}: {exc}")
            continue
        replayed += 1
        expectations = {
            "goal_sha256": outcome["goal_sha256"],
            "proof_sha256": outcome["proof_sha256"],
            "target_content_sha256": outcome["target_content_sha256"],
            "goal_binders": str(outcome["goal_binders"]),
            "holes": str(outcome["holes"]),
            "holes_matched": str(outcome["holes_matched"]),
            "declarations_tried": str(outcome["declarations_tried"]),
            "declarations": str(outcome["admitted_declarations"]),
            "axioms": "0",
            "theorem_dependencies": str(outcome["theorem_dependencies"]),
            "theorem_dependency_names": ",".join(outcome["theorem_dependency_names"]),
            "target_dependency": "false",
        }
        for key, expected in expectations.items():
            actual = fields.get(key)
            if actual != expected:
                failures.append(
                    f"{outcome['fact_id']}: {key} {actual!r} != pinned {expected!r}"
                )

    if replayed != len(manifest["outcomes"]):
        failures.append(
            f"replayed {replayed} of {len(manifest['outcomes'])} targets"
        )

    check_ledger(manifest, failures)

    if not args.quiet:
        print(
            f"NAT_MODEQ_CONGRUENCE|targets={len(manifest['outcomes'])}"
            f"|replayed={replayed}|failures={len(failures)}"
        )
    for failure in failures:
        print(f"NAT_MODEQ_CONGRUENCE|FAIL|{failure}", file=sys.stderr)
    if failures:
        print(
            f"NAT_MODEQ_CONGRUENCE|FAIL|{len(failures)} mismatch(es)", file=sys.stderr
        )
        return 1
    if not args.quiet:
        print("NAT_MODEQ_CONGRUENCE|PASS")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except CheckError as exc:
        print(f"NAT_MODEQ_CONGRUENCE|ERROR|{exc}", file=sys.stderr)
        sys.exit(2)
