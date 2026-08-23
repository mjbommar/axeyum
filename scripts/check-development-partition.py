#!/usr/bin/env python3
"""The development partition is unguarded, and it is the same hole one level down.

`check-autogenesis-holdout-isolation.py` closed the held-out hole after an
authoritative operation was registered against a held-out fact on 2026-08-21 and
spent 19 of the then-76 held-out propositions. That gate is thorough about
held-out and says **nothing about development**.

Measured 2026-08-22: 78 open facts sit in `development`
(natural-primes 21, natural-modular-equivalence 20, natural-bitwise 19,
natural-gcd 18) against **56 in `train`**. Development is larger than the entire
surface we are allowed to build on, and nothing stopped a producer being built
directly against it.

That is not the same error as a held-out breach, and it should not be gated the
same way. Development is *meant* to be settled -- that is what an evaluation
does. What must not happen is a producer being **built** on it, because a
producer tuned against the development set no longer measures generalization,
and the number it reports is the one number the split policy exists to make
trustworthy.

So the rule enforced here is a shape, not a prohibition:

  **An operation that closes a development fact must also close a train fact.**

An operation covering development and no train fact is a producer whose entire
applicability was authored against the evaluation set. An operation spanning
both is exactly the intended design -- build on train, demonstrate on
development -- and passes.

Two further properties:

  * **The generality ratchet.** The count of facts closed by operations covering
    more than one fact may never fall. 24 of 25 registered operations cover
    exactly one fact; a bespoke capsule converts an irreplaceable train row into
    a single theorem and teaches nothing. The ratchet cannot force generality,
    but it makes a regression loud. See `docs/autogenesis/239-the-train-budget.md`.

  * **The budget report.** Open counts per partition, printed always. Not
    gated -- a pinned count would fail on every legitimate landing and would be
    updated reflexively, which is how a gate becomes a formality.

EXEMPTIONS come only from recorded nursery amendments. A fact named in an
amendment's `breach` block is already spent and recorded; this gate exists to
prevent the NEXT one, not to relitigate a repair.

FAIL-CLOSED. An unreadable manifest, an empty development population, or an
operations registry that has become empty is an error. A guard whose subject has
vanished reports the same "no violations" as a guard that works -- this
repository has shipped that exact defect, 40 of 162 checker runs exiting 0 on
completion alone.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import sys
from typing import Any, Iterator

ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
SPLIT_POLICY = ROOT / "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
FACTS = ROOT / "artifacts/facts"

SETTLED = {"proved", "computed"}

# The ratchet floor: facts covered by operations of width > 1. Raise it when a
# family producer lands; it may never be lowered without deleting an operation,
# which is itself the regression this catches.
MULTI_TARGET_FLOOR = 5


class DevelopmentPartitionError(Exception):
    pass


def _load(path: pathlib.Path) -> Any:
    if not path.is_file():
        raise DevelopmentPartitionError(f"missing manifest: {path.relative_to(ROOT)}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise DevelopmentPartitionError(f"unreadable manifest {path.relative_to(ROOT)}: {exc}") from exc


def _strings(node: Any) -> Iterator[str]:
    """Every string anywhere in a JSON tree.

    Deliberately generic, for the reason the held-out gate gives: operations
    already carry fact ids at three distinct JSON paths, so a field-specific
    walk was bypassable the day it was written.
    """
    if isinstance(node, dict):
        for value in node.values():
            yield from _strings(value)
    elif isinstance(node, list):
        for value in node:
            yield from _strings(value)
    elif isinstance(node, str):
        yield node


def fact_partitions() -> dict[str, str]:
    """Partition per fact, from BOTH sources, requiring them to agree.

    The nursery records a `partition` on every entry AND the split policy
    records one per family. Measured 2026-08-22 the two agree on all 216 facts
    that have both (train 78, development 79, held-out 57), with `nat-bootstrap`
    carrying `longitudinal` and sitting outside the family policy by design.

    Two sources that can drift are a defect waiting to happen, and the drift
    would be silent: whichever file a reader consults would look authoritative.
    So disagreement is an ERROR here rather than a precedence rule -- picking a
    winner would hide exactly the edit that needs to be seen.
    """
    nursery = _load(NURSERY)
    policy = _load(SPLIT_POLICY)
    families = policy.get("family_partitions")
    if not isinstance(families, dict) or not families:
        raise DevelopmentPartitionError("split policy carries no family_partitions")
    entries = nursery.get("entries")
    if not isinstance(entries, list) or not entries:
        raise DevelopmentPartitionError("nursery carries no entries")

    out: dict[str, str] = {}
    disagreements: list[str] = []
    for entry in entries:
        fact_id = entry.get("fact_id") or entry.get("id")
        partition = entry.get("partition")
        family = entry.get("family")
        if not fact_id or not partition:
            raise DevelopmentPartitionError(
                f"nursery entry {fact_id or entry!r} carries no partition"
            )
        family_partition = families.get(family)
        if family_partition is not None and family_partition != partition:
            disagreements.append(
                f"{fact_id}: entry says {partition!r}, family {family!r} says {family_partition!r}"
            )
        out[fact_id] = partition
    if disagreements:
        raise DevelopmentPartitionError(
            "nursery and split policy disagree on "
            f"{len(disagreements)} fact(s): " + "; ".join(sorted(disagreements)[:5])
        )
    if not out:
        raise DevelopmentPartitionError("no nursery entry carried both a fact id and a partition")
    return out


def amended_fact_ids() -> set[str]:
    """Facts already spent by a recorded breach, and repaired by amendment."""
    nursery = _load(NURSERY)
    spent: set[str] = set()
    for amendment in nursery.get("amendments", []) or []:
        breach = amendment.get("breach")
        if isinstance(breach, dict):
            fact_id = breach.get("fact_id")
            if isinstance(fact_id, str):
                spent.add(fact_id)
    return spent


def fact_statuses() -> dict[str, str]:
    if not FACTS.is_dir():
        raise DevelopmentPartitionError("artifacts/facts is not a directory")
    out: dict[str, str] = {}
    for path in sorted(FACTS.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DevelopmentPartitionError(f"unreadable fact {path.name}: {exc}") from exc
        out[data["id"]] = data["epistemic_status"]
    if not out:
        raise DevelopmentPartitionError("no facts read")
    return out


def check(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    partitions = fact_partitions()
    exempt = amended_fact_ids()
    statuses = fact_statuses()
    registry = _load(OPERATIONS).get("operations")
    if not isinstance(registry, list) or not registry:
        raise DevelopmentPartitionError("operations registry is empty or malformed")

    development = {f for f, p in partitions.items() if p == "development"}
    if not development:
        raise DevelopmentPartitionError("development population is empty — the gate has no subject")

    violations: list[str] = []
    multi_target_facts: set[str] = set()

    for operation in registry:
        op_id = operation.get("id", "<unnamed>")
        referenced = {s for s in _strings(operation) if s in partitions}
        touched_dev = {f for f in referenced if partitions[f] == "development"} - exempt
        touched_train = {f for f in referenced if partitions[f] == "train"}
        if touched_dev and not touched_train:
            violations.append(
                f"{op_id} references development fact(s) {sorted(touched_dev)} "
                f"and no train fact — a producer authored against the evaluation set"
            )
        fact_ids = operation.get("applicability", {}).get("fact_ids", [])
        if len(fact_ids) > 1:
            multi_target_facts.update(fact_ids)

    covered = len(multi_target_facts)
    if covered < MULTI_TARGET_FLOOR:
        violations.append(
            f"generality ratchet: {covered} facts covered by multi-target operations, "
            f"floor is {MULTI_TARGET_FLOOR} — an operation was narrowed or deleted"
        )

    if not args.quiet:
        counts: dict[str, int] = {}
        for fact, partition in partitions.items():
            if statuses.get(fact) not in SETTLED:
                counts[partition] = counts.get(partition, 0) + 1
        budget = " ".join(
            f"{k}={counts.get(k, 0)}" for k in ("train", "development", "held-out", "longitudinal")
        )
        print(f"DEVELOPMENT_PARTITION|open|{budget}")
        print(
            f"DEVELOPMENT_PARTITION|operations={len(registry)}"
            f"|multi_target_facts={covered}|floor={MULTI_TARGET_FLOOR}"
            f"|exempt_by_amendment={len(exempt)}"
        )

    for violation in violations:
        print(f"DEVELOPMENT_PARTITION|VIOLATION|{violation}", file=sys.stderr)
    if violations:
        print(
            f"DEVELOPMENT_PARTITION|FAIL|{len(violations)} violation(s)",
            file=sys.stderr,
        )
        return 1
    if not args.quiet:
        print("DEVELOPMENT_PARTITION|PASS")
    return 0


def main() -> int:
    try:
        return check()
    except DevelopmentPartitionError as exc:
        print(f"DEVELOPMENT_PARTITION|ERROR|{exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
