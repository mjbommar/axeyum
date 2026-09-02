#!/usr/bin/env python3
"""Independently re-derive and check the Nat.bit constructor family operation.

`authoritative-mathlib-nat-bit-constructor-family-v1` closes four previously
open sibling facts of draw 19's `natural-bit-constructor` family (ADR-1561,
primary module `Mathlib.Data.Nat.BinaryRec`) with ONE target-agnostic
producer and no per-target proof code:
`axeyum_lean_import::producers::bounded_induction::propose_bounded_induction`
(peel the leading telescope, `Eq.refl` at the terminal, and where that is
stuck one bounded structural induction plus one congruence rewrite driven by
the induction hypothesis).

WHAT THIS GATE'S EXIT STATUS DEPENDS ON. Four findings, each able to fail:

  1. **The four accepts still replay.** Every target is re-run through
     `bounded_induction_operation` from its tracked, hash-pinned Mathlib
     export, and every receipt field must equal the committed candidate
     manifest -- goal digest, proof digest, target-content digest, binders,
     inductions, admitted declarations, and zero for axioms / theorem
     dependencies / target dependency / ledger writes. A changed proof term,
     a changed export, or a producer that started citing a theorem all fail
     here.
  2. **The four facts are still bound to this operation.** Each must be
     `proved` via `kernel-lean` with an EMPTY axiom footprint and exactly one
     `checked` evidence row whose `checker_operation.id` is this operation,
     and no other fact the operation names may carry a second row.
  3. **The six declines still decline, and their facts are still open.** The
     family has ten members; six were NOT closed. This gate re-runs the
     producer on each of the six from its own tracked export and requires the
     recorded typed decline class to reproduce. This is the half of the
     population a "coverage" number would quietly drop: a producer that
     suddenly admitted `Nat.bit b n / 2 = n` without anyone updating this file
     would be admitting a goal nobody re-reviewed, and a fact flipped by some
     other route while this artifact still calls it declined is a stale claim
     of the exact kind ADR-1510 rule 2 exists to catch.
  4. **The outcome-blind mutation control still declines.** `n! = 0` is FALSE
     by construction (`F:ml430-mutation-7afa5ec620720a1501bf349d`); if the
     producer ever admits it, this whole census is void, and the gate says so
     rather than passing. A nonexistent input path is probed too, because a
     tool that ignored its argument would satisfy every check above for the
     wrong reason.

A checker that cannot fail is worse than no checker (CLAUDE.md), so this
script fails loudly and specifically on any of the four rather than reporting
completion alone.

MUTATION CONTROL, RUN 2026-09-02, one mutation per finding. Each was applied
to the committed tree, this gate was run, and the mutation reverted. All four
turned the gate red, so no finding above is decoration:

  | finding | mutation                                    | exit | error |
  | ------- | ------------------------------------------- | ---- | ----- |
  | 1       | `bit-true` manifest `proof_sha256` -> zeros  | 1 | `replayed receipt disagrees` |
  | 2       | `F:ml430-nat-bit-true-...` footprint `["propext"]` | 1 | `axiom footprint is not empty` |
  | 3       | `F:ml430-nat-bit-div-two-...` set `proved`   | 1 | `recorded as DECLINED ... ledger now says 'proved'` |
  | 4       | the FALSE mutation control set `proved`      | 1 | `expected to remain open (it is FALSE)` |

Re-run with the harness recorded in ADR-1570; it is four edit/run/revert
cycles over this gate and needs no new fixture.
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
OPERATION_ID = "authoritative-mathlib-nat-bit-constructor-family-v1"
DRIVER = "axeyum-lean-import/bounded-induction-multi-target-v1"

SETTLED_FACT_IDS = (
    "F:ml430-nat-bit-false-98b0bf2a",
    "F:ml430-nat-bit-false-apply-5962146d",
    "F:ml430-nat-bit-true-2456e237",
    "F:ml430-nat-bit-true-apply-02338ebc",
)

FAMILY_SOURCE_ROOT = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/sources/"
    "mathlib-v4.30.0-nat-bit-constructor-family-v1"
)
NAMESPACE = "Axeyum.Autogenesis.Statement.NatBitFamily"

# The SIX family members this producer does NOT close, with the decline class
# each one reproduced on 2026-09-02. `import` means the failure happened in
# `import_statement_ndjson` before the producer ran at all; `producer` means
# the bounded chain ran and declined. Keeping this table here -- rather than
# only in the decline artifacts -- is what lets the gate notice a member that
# silently started passing or silently got closed by another route.
DECLINED: tuple[tuple[str, str, str, str, str], ...] = (
    (
        "bit-div-two",
        "bitDivTwo",
        "F:ml430-nat-bit-div-two-d74e7898",
        "producer",
        "terminal goal is not definitionally equal and no applicable "
        "induction-hypothesis rewrite closed the gap",
    ),
    (
        "bit-eq-zero-iff",
        "bitEqZeroIff",
        "F:ml430-nat-bit-eq-zero-iff-6b701e2b",
        "producer",
        "terminal goal is not an exact Eq application after transparent reduction",
    ),
    (
        "bit-mod-two-eq-one-iff",
        "bitModTwoEqOneIff",
        "F:ml430-nat-bit-mod-two-eq-one-iff-d9b00bec",
        "producer",
        "terminal goal is not an exact Eq application after transparent reduction",
    ),
    (
        "bit-mod-two-eq-zero-iff",
        "bitModTwoEqZeroIff",
        "F:ml430-nat-bit-mod-two-eq-zero-iff-b69a9790",
        "producer",
        "terminal goal is not an exact Eq application after transparent reduction",
    ),
    (
        "bit-ne-zero-iff",
        "bitNeZeroIff",
        "F:ml430-nat-bit-ne-zero-iff-d811128e",
        "producer",
        "terminal goal is not an exact Eq application after transparent reduction",
    ),
    (
        "bitwise-zero",
        "bitwiseZero",
        "F:ml430-nat-bitwise-zero-7c0e3f82",
        "import",
        'TrustedDeclaration { name: "dif_pos", kind: Theorem }',
    ),
)

NEGATIVE_CONTROL_STREAM = pathlib.Path(
    "/nas3/data/axeyum/autogenesis/coverage/"
    "26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r046.ndjson"
)
NEGATIVE_CONTROL_TARGET = "Axeyum.Autogenesis.Coverage.r046"
NEGATIVE_CONTROL_FACT_ID = "F:ml430-mutation-7afa5ec620720a1501bf349d"

OPEN_STATUSES = {"open", "conjectured", "empirical"}


class FamilyError(RuntimeError):
    """The Nat.bit constructor family no longer has its checked meaning."""


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


def load_fact(fact_id: str) -> dict[str, Any]:
    return load(ROOT / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json"))


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


def run_producer(artifact: pathlib.Path, target: str) -> subprocess.CompletedProcess:
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
        timeout=600,
    )


def load_operation() -> dict[str, Any]:
    registry_checker = load_module(
        "nat_bit_family_registry", ROOT / "scripts/validate-autogenesis-operations.py"
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
    """Finding 1, per target: the accept still replays, bit for bit."""
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

    fact = load_fact(fact_id)
    statement = (fact.get("formal") or {}).get("statement")
    if not isinstance(statement, str) or sha256_text(statement) != adapter.get(
        "source_statement_sha256"
    ):
        raise FamilyError(f"{fact_id}: statement identity disagrees with its fact")

    artifact = validate_external(adapter["external_artifact"])
    completed = run_producer(artifact, target["target_definition"])
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
        raise FamilyError(
            f"{fact_id}: replayed receipt disagrees: {observed!r} != {expected!r}"
        )
    if sha256_text(receipt["goal"]) != op["goal_sha256"]:
        raise FamilyError(f"{fact_id}: rendered goal digest disagrees")
    if sha256_text(receipt["proof"]) != op["proof_sha256"]:
        raise FamilyError(f"{fact_id}: rendered proof digest disagrees")


def check_settled_fact_binding(operation: dict[str, Any]) -> None:
    """Finding 2: the four facts are proved, axiom-free, and bound here once."""
    settled = set(SETTLED_FACT_IDS)
    all_named = operation["applicability"]["fact_ids"]
    if set(all_named) != settled:
        raise FamilyError(
            "SETTLED_FACT_IDS and applicability.fact_ids disagree: "
            f"{sorted(settled ^ set(all_named))}"
        )
    for fact_id in SETTLED_FACT_IDS:
        fact = load_fact(fact_id)
        if (
            fact.get("epistemic_status") != "proved"
            or fact.get("proof_route") != "kernel-lean"
        ):
            raise FamilyError(f"{fact_id}: not settled as expected")
        if fact.get("axiom_footprint") != []:
            raise FamilyError(f"{fact_id}: axiom footprint is not empty")
        rows = [
            row
            for row in fact.get("evidence", [])
            if isinstance(row, dict)
            and isinstance(row.get("checker_operation"), dict)
            and row["checker_operation"].get("id") == OPERATION_ID
        ]
        if len(rows) != 1:
            raise FamilyError(
                f"{fact_id}: expected exactly one evidence row bound to "
                f"{OPERATION_ID}, found {len(rows)}"
            )
        if rows[0].get("check_status") != "checked":
            raise FamilyError(f"{fact_id}: bound evidence row is not checked")


def check_declines() -> None:
    """Finding 3: the six non-closures still decline, and are still open.

    The population this gate reports on is the WHOLE family of ten, not the
    four it closed. A blind spot on the six is how a coverage number becomes
    a claim nobody can falsify.
    """
    for slug, definition, fact_id, stage, message in DECLINED:
        fact = load_fact(fact_id)
        status = fact.get("epistemic_status")
        if status not in OPEN_STATUSES:
            raise FamilyError(
                f"{fact_id}: recorded as DECLINED by this producer but the "
                f"ledger now says {status!r} -- another route closed it and this "
                "family's decline record is stale (ADR-1510 rule 2)"
            )
        artifact = FAMILY_SOURCE_ROOT / f"{slug}.ndjson"
        if not artifact.is_file():
            raise FamilyError(f"{fact_id}: decline export missing: {artifact}")
        completed = run_producer(artifact, f"{NAMESPACE}.{definition}")
        if completed.returncode == 0:
            raise FamilyError(
                f"{fact_id}: the producer now ADMITS a goal this family records "
                "as declined -- the decline table is stale and the new proof has "
                "not been reviewed"
            )
        if message not in completed.stderr:
            raise FamilyError(
                f"{fact_id}: declined for a different reason than recorded "
                f"({stage}): {completed.stderr.strip()}"
            )


def check_negative_control() -> None:
    """Finding 4: a FALSE proposition is still refused, and the tool reads its
    argument."""
    if not NEGATIVE_CONTROL_STREAM.is_file():
        raise FamilyError(f"negative control stream missing: {NEGATIVE_CONTROL_STREAM}")
    fact = load_fact(NEGATIVE_CONTROL_FACT_ID)
    if fact.get("epistemic_status") != "open":
        raise FamilyError(
            f"{NEGATIVE_CONTROL_FACT_ID}: expected to remain open (it is FALSE)"
        )
    completed = run_producer(NEGATIVE_CONTROL_STREAM, NEGATIVE_CONTROL_TARGET)
    if completed.returncode == 0:
        raise FamilyError(
            "VOID: the negative control (a FALSE outcome-blind mutation) was "
            "ADMITTED by the bounded-induction checker. This census is void."
        )
    if "producer declined" not in completed.stderr:
        raise FamilyError(
            f"negative control failed for the wrong reason: {completed.stderr.strip()}"
        )
    bogus = ROOT / "artifacts/autogenesis/does-not-exist-nat-bit-family-probe.ndjson"
    if bogus.exists():
        raise FamilyError("probe path unexpectedly exists; pick a different name")
    if run_producer(bogus, NEGATIVE_CONTROL_TARGET).returncode == 0:
        raise FamilyError("the bounded-induction checker ignored a nonexistent path")


def main() -> int:
    try:
        operation = load_operation()
        executor = operation["executor"]
        if executor["driver"] != DRIVER:
            raise FamilyError("operation driver changed")
        targets = executor["targets"]
        if len(targets) != len(SETTLED_FACT_IDS):
            raise FamilyError(
                f"expected exactly {len(SETTLED_FACT_IDS)} targets in this family"
            )
        for target in targets:
            check_target(target, executor["max_binders"], executor["max_inductions"])
        check_settled_fact_binding(operation)
        check_declines()
        check_negative_control()
        print(
            "AUTOGENESIS_NAT_BIT_CONSTRUCTOR_FAMILY_OK|"
            f"operation={OPERATION_ID}|family_members={len(SETTLED_FACT_IDS) + len(DECLINED)}|"
            f"accepted={len(targets)}|declined={len(DECLINED)}|"
            f"settled_facts={','.join(SETTLED_FACT_IDS)}|"
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
        print(f"AUTOGENESIS_NAT_BIT_CONSTRUCTOR_FAMILY_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
