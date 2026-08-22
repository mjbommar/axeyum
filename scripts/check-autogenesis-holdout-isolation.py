#!/usr/bin/env python3
"""The held-out partition must stay blind, and prose did not keep it that way.

`docs/autogenesis/16-mathlib-frozen-nursery-split-result.md` preregistered 214
propositions into train / development / held-out, and the programme README
promises that "every policy improvement is evaluated against immutable held-out
populations." On 2026-08-21 an authoritative operation was registered against
`F:ml430-nat-gcd-greatest-0a04214a`, a held-out fact, and it stayed unnoticed
until 2026-08-22 because **nothing checked**:
`check-autogenesis-nursery.py` validates the manifest's internal integrity and
never inspects what operations do to it, and `validate-autogenesis-operations.py`
did not mention partitions at all. The split key is `<family>:<statement-shape>`
and the declared partition unit is the whole family, so one row spent 19 of the
then-76 held-out propositions -- 25% of the partition.

This gate closes that hole from both directions:

1.  **No held-out fact may be settled in the ledger.** Establishing a held-out
    proposition by ANY route spends it; the operation registry is only one way
    in, so checking the registry alone would leave the others open.
2.  **No artifact may reference a held-out fact id**, except the two files that
    define the population itself. A generic walk is used rather than a check on
    `applicability.fact_ids`: operations already carry fact ids at three
    distinct JSON paths (`applicability.fact_ids[]`, `executor.input_fact_id`,
    `executor.premise_fact_id`), so a field-specific guard was bypassable the
    day it was written, and a schema addition would silently reopen it.

FAIL-CLOSED. An unreadable manifest, or a held-out population that has somehow
become empty, is an error rather than a quiet pass -- a guard whose subject has
vanished reports the same "no violations" as a guard that works.
"""

from __future__ import annotations

import json
import pathlib
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
FACTS = ROOT / "artifacts/facts"
ARTIFACTS = ROOT / "artifacts/autogenesis"

# The two files that DEFINE the held-out population necessarily name its members.
POPULATION_FILES = {"nursery-v1.json", "mathlib-nat-int-fact-catalog-v1.json"}
SETTLED = {"proved", "computed"}


class IsolationError(Exception):
    pass


def held_out_facts() -> set[str]:
    if not NURSERY.is_file():
        raise IsolationError(f"nursery manifest is missing: {NURSERY}")
    try:
        manifest = json.loads(NURSERY.read_text())
    except json.JSONDecodeError as error:
        raise IsolationError(f"nursery manifest is unreadable: {error}") from error
    entries = manifest.get("entries")
    if not isinstance(entries, list):
        raise IsolationError("nursery manifest has no entries")
    held = {
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict) and entry.get("partition") == "held-out"
    }
    if not held:
        raise IsolationError(
            "the held-out population is empty; this gate would pass vacuously"
        )
    return held


def strings(value: Any, path: str) -> list[tuple[str, str]]:
    if isinstance(value, dict):
        return [x for k, v in value.items() for x in strings(v, f"{path}.{k}")]
    if isinstance(value, list):
        return [x for v in value for x in strings(v, f"{path}[]")]
    if isinstance(value, str):
        return [(value, path)]
    return []


def main() -> int:
    try:
        held = held_out_facts()
    except IsolationError as error:
        print(f"AUTOGENESIS_HOLDOUT_ISOLATION_ERROR|{error}", file=sys.stderr)
        return 1

    violations: list[str] = []

    # (1) settled held-out facts
    settled = []
    for fact_id in sorted(held):
        path = FACTS / (fact_id.replace("F:", "F-") + ".json")
        if not path.is_file():
            continue
        status = json.loads(path.read_text()).get("epistemic_status")
        if status in SETTLED:
            settled.append(f"{fact_id} is {status}")
    violations += [f"settled-held-out-fact|{item}" for item in settled]

    # (2) references from anywhere else
    scanned = 0
    for path in sorted(ARTIFACTS.glob("*.json")):
        if path.name in POPULATION_FILES:
            continue
        try:
            document = json.loads(path.read_text())
        except json.JSONDecodeError:
            continue
        scanned += 1
        for value, where in strings(document, ""):
            if value in held:
                violations.append(f"held-out-reference|{path.name}{where}|{value}")

    verdict = "FAIL" if violations else "PASS"
    print(
        f"AUTOGENESIS_HOLDOUT_ISOLATION|held_out={len(held)}|"
        f"files_scanned={scanned}|settled={len(settled)}|"
        f"references={len(violations) - len(settled)}|verdict={verdict}"
    )
    for item in violations:
        print(f"  {item}", file=sys.stderr)
    if violations:
        print(
            "held-out isolation is spent by any of these; the repair is an amendment "
            "in artifacts/autogenesis/mathlib-nursery-split-policy-v1.json, not a "
            "deletion -- see docs/autogenesis/"
            "226-production-measurement-and-general-producer-plan.md",
            file=sys.stderr,
        )
    return 1 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
