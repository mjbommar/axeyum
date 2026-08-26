#!/usr/bin/env python3
"""Independently re-derive and check the Nat.ModEq-family targets.

This checker's three Nat.ModEq targets are named by the SAME registered
operation as the Int.ModEq family, `authoritative-mathlib-modeq-family-v1`
(originally registered separately as `authoritative-mathlib-nat-modeq-family-v1`;
merged 2026-08-25 -- see `scripts/check-development-partition.py`, which
requires an operation naming a `development` fact to also name a `train`
fact, and this producer's Int.ModEq facts are exactly the train facts it
generalizes from, established first). The merge changed only the registry
entry these facts are named under; the producer/checker pair, the goals, the
proofs and every replayed digest below are unchanged.

That producer/checker pair (`producers::modeq_family` /
`modeq_family_operation.rs`) never names `Int`, `Nat`, `ModEq`, or `%` -- it
peels `Pi` binders into hypotheses and closes an `Eq`- or `Iff`-headed
terminal goal by `refl`/`symm`/`trans`/`Iff.intro` alone, all reconstructed
from `Eq.rec`/`Iff`'s own constructor. `Nat.ModEq n a b` unfolds transparently
to the same `a % n = b % n` shape as `Int.ModEq`, so this is a BLIND
generalization probe, not a new producer: `docs/autogenesis/242-nat-division-
gates-modular-arithmetic.md` records that all four `natural-modular-
equivalence` (development) streams import cleanly with zero axioms, and this
script confirms the same bounded search actually closes three of the four --
`Nat.ModEq.refl`, `Nat.ModEq.symm`, `Nat.ModEq.trans` -- from their
tracked, hash-pinned external Mathlib exports.

The fourth member, `Nat.ModEq.comm` (`F:ml430-nat-modeq-comm-24b71e7a`), was
initially deferred because its ledger dependency on `Nat.ModEq.symm` was open.
The authoritative loop admitted symmetry and transitivity on 2026-08-25, then
recomputed the frontier and found commutativity dependency-ready. It is now the
fourth Nat target of the same unchanged producer; this extension records a real
durable-state-to-next-dispatch transition rather than bypassing the dependency.

Registering this operation does not by itself prove anything: it makes three
`open` facts dispatchable to `fact-frontier.py`'s selection. `execute-
autogenesis-operation.py` cannot carry that dispatch through to a ledger
write for THIS operation -- `selected_inputs()` requires the frontier's
`admissible_fact_ids` to equal exactly `[selected_fact_id]`, and as long as
two or more of the three facts this operation names remain simultaneously
open and dependency-ready, the frontier's admissible set has more than one
member and the automated executor refuses categorically, before even
reaching driver dispatch (which also has no handler registered for
`axeyum-lean-import/modeq-family-multi-target-v1`). So promotion here is the
same hand-authored-commit-following-independently-rechecked-receipt pattern
already used for the operation's Int.ModEq facts (`6b8c2526b`): the checker
in this file re-derives the receipt independently of any ledger claim, and a
human- or agent-reviewed commit is what actually flips a fact's
`epistemic_status`, one fact at a time so the transition stays reviewable.

`F:ml430-nat-modeq-refl-d870c8f5` was flipped `proved` this way, with an
evidence row bound to `authoritative-mathlib-modeq-family-v1`'s id (recorded
at the time as `authoritative-mathlib-nat-modeq-family-v1`, before the merge
above; only the id string changed), `checker_operation.goal_sha256` and
`proof_sha256` matching exactly what `check_target` below re-derives.
`F:ml430-nat-modeq-symm-0a3d4d18` and `F:ml430-nat-modeq-trans-ef9d1c46`
were subsequently closed through the typed execution and transaction path.
`F:ml430-nat-modeq-comm-24b71e7a` is the remaining dispatchable target.
A registration gate that let an `open` fact drift to `proved` without a
matching evidence row, or let a `proved` fact's evidence disagree with a
fresh replay, would be exactly the "checker that cannot fail" defect this
ledger tracks -- so this script checks both states explicitly.

A checker that cannot fail is worse than no checker, so this script fails
loudly on any mismatch rather than reporting completion alone: every field
of the replayed receipt is compared against the committed candidate manifest
exactly, the external Mathlib exports are hash- and permission-pinned, the
checker's circularity guard is re-run via its own adversarial fixture (the
producer is unmodified from the `Int.ModEq` operation, so mirroring that
fixture again here would just be a second, weaker copy of the same
kernel-level check), and the checker is confirmed to decline on a
nonexistent input path.
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
# Merged 2026-08-25 into the Int.ModEq operation so the development-partition
# gate sees a train fact alongside these development facts (see module
# docstring). The registered id under which these three facts were originally
# closed was `authoritative-mathlib-nat-modeq-family-v1`; the fact ledger's
# already-written evidence for `F:ml430-nat-modeq-refl-d870c8f5` was updated
# to match.
OPERATION_ID = "authoritative-mathlib-modeq-family-v1"
DISPATCHABLE_FACT_IDS = (
    "F:ml430-nat-modeq-refl-d870c8f5",
    "F:ml430-nat-modeq-symm-0a3d4d18",
    "F:ml430-nat-modeq-trans-ef9d1c46",
    "F:ml430-nat-modeq-comm-24b71e7a",
)
SETTLED_FACT_IDS = (
    "F:ml430-nat-modeq-refl-d870c8f5",
    "F:ml430-nat-modeq-symm-0a3d4d18",
    "F:ml430-nat-modeq-trans-ef9d1c46",
)
REMAINING_DISPATCHABLE_FACT_IDS = ("F:ml430-nat-modeq-comm-24b71e7a",)


class FamilyError(RuntimeError):
    """The Nat.ModEq family no longer has its checked meaning."""


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
        "nat_modeq_family_registry", ROOT / "scripts/validate-autogenesis-operations.py"
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


def check_target(target: dict[str, Any], max_binders: int) -> dict[str, Any]:
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
    return modeq


def check_registration_grants_dispatch_not_proof(
    operation: dict[str, Any], targets_by_fact: dict[str, dict[str, Any]]
) -> None:
    """This operation makes three facts dispatchable; registration alone must
    not have proved any of them, and a promotion must carry an evidence row
    that agrees exactly with a fresh replay. A registration gate that
    tolerated a status flip without a real, matching evidence row -- in
    either direction -- would be exactly the checker-that-cannot-fail defect
    this ledger tracks, moved one arrow upstream."""
    dispatchable = set(DISPATCHABLE_FACT_IDS)
    all_named = operation["applicability"]["fact_ids"]
    # A containment check, not equality: this operation also names its four
    # Int.ModEq train facts (see module docstring), so applicability.fact_ids
    # is a strict superset of DISPATCHABLE_FACT_IDS, not equal to it.
    if not dispatchable <= set(all_named):
        raise FamilyError(
            f"DISPATCHABLE_FACT_IDS {sorted(dispatchable)} missing from "
            f"applicability.fact_ids {sorted(all_named)}"
        )
    if set(SETTLED_FACT_IDS) | set(REMAINING_DISPATCHABLE_FACT_IDS) != dispatchable:
        raise FamilyError(
            "SETTLED_FACT_IDS and REMAINING_DISPATCHABLE_FACT_IDS no longer "
            "partition DISPATCHABLE_FACT_IDS"
        )
    for fact_id in REMAINING_DISPATCHABLE_FACT_IDS:
        fact = load(ROOT / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json"))
        if fact.get("epistemic_status") != "open":
            raise FamilyError(
                f"{fact_id}: expected epistemic_status 'open' (registration is not "
                f"proof); found {fact.get('epistemic_status')!r}"
            )
        rows = [
            row
            for row in fact.get("evidence", [])
            if isinstance(row, dict)
            and isinstance(row.get("checker_operation"), dict)
            and row["checker_operation"].get("id") == OPERATION_ID
        ]
        if rows:
            raise FamilyError(
                f"{fact_id}: an 'open' fact must carry no evidence row bound to "
                f"{OPERATION_ID}; found {len(rows)}"
            )
    for fact_id in SETTLED_FACT_IDS:
        target = targets_by_fact[fact_id]
        op = target["modeq"].get("operation") or {}
        fact = load(ROOT / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json"))
        if fact.get("epistemic_status") != "proved" or fact.get("proof_route") != "kernel-lean":
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
        row = rows[0]
        if row.get("check_status") != "checked":
            raise FamilyError(f"{fact_id}: bound evidence row is not checked")
        bound = row["checker_operation"]
        for key in (
            "goal_sha256",
            "proof_sha256",
            "target_content_sha256",
            "binders_used",
            "admitted_declarations",
            "target_definition",
        ):
            if bound.get(key) != op.get(key):
                raise FamilyError(
                    f"{fact_id}: evidence row {key}={bound.get(key)!r} disagrees "
                    f"with the freshly replayed {key}={op.get(key)!r}"
                )
    comm = load(
        ROOT
        / "artifacts/facts"
        / "F-ml430-nat-modeq-comm-24b71e7a.json"
    )
    if comm.get("depends_on") != ["F:ml430-nat-modeq-symm-0a3d4d18"]:
        raise FamilyError(
            "Nat.ModEq.comm: expected dependency changed; re-check the durable "
            "unlock before retaining it in this operation"
        )


def check_circularity_adversarial_control() -> None:
    """The negative control for THIS producer's actual failure mode: a
    candidate that closes its goal by citing the target theorem itself. The
    producer is unmodified from the `Int.ModEq` operation, so this is the
    same fixture re-run rather than duplicated -- see the module docstring."""
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
    bogus = ROOT / "artifacts/autogenesis/does-not-exist-nat-modeq-family-probe.ndjson"
    if bogus.exists():
        raise FamilyError("probe path unexpectedly exists; pick a different name")
    completed = run_checker(bogus, target_definition)
    if completed.returncode == 0:
        raise FamilyError("the nat-modeq-family checker ignored a nonexistent input path")


def main() -> int:
    try:
        operation = load_operation()
        executor = operation["executor"]
        if executor["driver"] != "axeyum-lean-import/modeq-family-multi-target-v1":
            raise FamilyError("operation driver changed")
        max_binders = executor["max_binders"]
        # The operation also carries the four Int.ModEq train targets (see
        # module docstring); this checker's job is the four Nat.ModEq
        # targets specifically, so it selects its own subset rather than
        # assuming the operation names only them.
        all_targets = executor["targets"]
        targets = [t for t in all_targets if t["fact_id"] in DISPATCHABLE_FACT_IDS]
        if len(targets) != 4:
            raise FamilyError("expected exactly four Nat targets in this family")
        targets_by_fact: dict[str, dict[str, Any]] = {}
        for target in targets:
            modeq = check_target(target, max_binders)
            targets_by_fact[target["fact_id"]] = {"modeq": modeq}
        check_registration_grants_dispatch_not_proof(operation, targets_by_fact)
        check_circularity_adversarial_control()
        check_bogus_path_declines(targets[0]["target_definition"])
        print(
            "AUTOGENESIS_NAT_MODEQ_FAMILY_OK|"
            f"operation={OPERATION_ID}|targets={len(targets)}|"
            f"settled_facts={','.join(SETTLED_FACT_IDS)}|"
            f"remaining_dispatchable_facts={','.join(REMAINING_DISPATCHABLE_FACT_IDS)}|"
            "deferred_fact=none|"
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
        print(f"AUTOGENESIS_NAT_MODEQ_FAMILY_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
