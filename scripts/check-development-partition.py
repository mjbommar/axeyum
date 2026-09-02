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

# NOT a single `nursery-v1.json` literal. Measured 2026-09-02:
# `authoritative-mathlib-nat-bit-constructor-family-v1` (ADR-1570) closed four
# `development` facts -- `F:ml430-nat-bit-false-98b0bf2a`,
# `F:ml430-nat-bit-false-apply-5962146d`, `F:ml430-nat-bit-true-2456e237`,
# `F:ml430-nat-bit-true-apply-02338ebc` -- and no train fact. All four live
# ONLY in `nursery-v2-extension.json`; this gate's old single-file `NURSERY`
# constant never opened it, so the dev-only rule below never saw them and the
# gate printed PASS. This is the third reader with the v1-only literal found
# in one day (`fact-frontier.py` and `SeedContractHoldoutIsolationTests` were
# the first two, both already fixed the same way): the manifest set is
# DERIVED, not named, mirroring `check-partition-edges.py`'s `MANIFEST_GLOBS`
# -- the v1 split plus any `nursery-v*-extension.json` refill, so a future
# `nursery-v3-extension.json` is found without editing this file again, and an
# unrelated decoy (`nursery-zzz-notes.json`) is not.
NURSERY_DIR = ROOT / "artifacts/autogenesis"
MANIFEST_GLOBS = ("nursery-v1.json", "nursery-v*-extension.json")
SPLIT_POLICY = ROOT / "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json"
OPERATIONS = ROOT / "artifacts/autogenesis/operations.json"
FACTS = ROOT / "artifacts/facts"

SETTLED = {"proved", "computed"}

# The ratchet floor: facts covered by operations of width > 1. Raise it when a
# family producer lands; it may never be lowered without deleting an operation,
# which is itself the regression this catches.
MULTI_TARGET_FLOOR = 5

# GRANDFATHERED OPERATIONS (ADR-1563). An operation named here is excused from
# the train-coverage rule. It is a CLOSED LIST IN SOURCE, not a data file, so
# joining it is a reviewed code change with an ADR behind it rather than an
# artifact edit a producer lane can make to clear its own gate -- which is the
# whole difference between this and the component exemption ADR-1546 measured
# growing 228 -> 274 to fit whatever had just failed.
#
# WHY A GRANDFATHER AND NOT ADR-1510 RETIREMENT. The obvious repair -- retire
# the operation the way `gen-obstruction-producers.py` retires a fulfilled
# contract -- IS NOT AVAILABLE HERE, and the reason is mechanical rather than a
# matter of taste. `scripts/check-autogenesis-fact-operation.py` pins
# `operation_sha256 = digest(operation)` INSIDE the evidence of every fact the
# operation admitted, and requires the fact's id to appear in the live
# `applicability.fact_ids`. Measured 2026-09-02 for
# `authoritative-mathlib-nat-modeq-remainder-family-v1`: the live digest is
# `cc868669…`, exactly what all three facts record, and adding a single
# `lifecycle` key moves it to `d610b146…`. So the operation can be neither
# edited nor deleted without breaking three `proved` facts' evidence. An
# operation is a RECEIPT (ADR-0602) and a receipt is immutable by construction;
# the lifecycle a contract has, it does not have.
#
# THE ENTRY IS NOT TAKEN ON ITS WORD. `grandfather_holds` re-derives two
# properties per entry, and an entry that fails either is NOT honoured:
#
#   1. every development fact the operation references is SETTLED, so a
#      grandfather can never cover live development work; and
#   2. every one of those facts pins THIS operation in its own evidence, which
#      is the property that makes retirement impossible and is therefore the
#      actual justification rather than a restatement of it.
#
# An entry that fires on nothing is itself a violation (`unused grandfather`),
# so the list self-retires the moment its subject changes shape -- the same
# discipline `check-autogenesis-nursery.py` applies to a stale component
# exemption.
#
# THIS DOES NOT WEAKEN THE RULE FOR FUTURE PRODUCERS. A new operation
# referencing development facts and no train fact still fails, because it is
# not in this dict; property 2 would also be false for it at registration time,
# when its targets are open and pin nothing.
GRANDFATHERED_OPERATIONS: dict[str, dict[str, str]] = {
    "authoritative-mathlib-nat-modeq-remainder-family-v1": {
        "registered": "9943ae6bd (2026-08-26)",
        "authority": "docs/research/09-decisions/adr-1563-the-bootstrap-lemma-"
                     "is-not-a-leak-and-the-stale-exemption-is-retired.md",
        "reason": "Three `natural-modular-equivalence` development targets and "
                  "no train fact. NOT a pre-rule landing -- this gate shipped "
                  "2026-08-22 in `50307d833`, four days earlier, and the three "
                  "facts were already `development` in the manifest at "
                  "registration; the gate was red and the operation landed "
                  "anyway. It cannot be repaired now because every one of the "
                  "three facts pins `operation_sha256` over this exact object.",
    },
    "authoritative-mathlib-nat-bit-constructor-family-v1": {
        "registered": "d11173b9d (2026-09-02)",
        "authority": "docs/research/09-decisions/adr-1570-one-operation-"
                     "closed-four-sibling-facts-and-the-other-six-say-what-"
                     "is-missing.md",
        "reason": "Four `natural-bit-constructor` development targets and no "
                  "train fact. This gate could not see the operation at "
                  "registration (its `NURSERY` constant read `nursery-v1.json` "
                  "alone and all four targets live only in "
                  "`nursery-v2-extension.json`), so it was red at the time "
                  "under the rule this loader fix now makes visible -- ADR-1570 "
                  "recorded the finding and deliberately left the loader and "
                  "the operation's disposition to a later lane rather than "
                  "fixing the gate that would have flagged its own change. "
                  "The measurement it made still holds: the entire live train "
                  "population is 17 open rows (5 outcome-blind mutation "
                  "controls, 2 divergence-blocked, 10 `natural-binomial-"
                  "bounds`), and no reflexivity-or-bounded-induction chain "
                  "proves `Nat.choose n k <= 2 ^ n` -- named there as this "
                  "contract's second non-example, and re-confirmed here "
                  "2026-09-02: across BOTH manifests (this loader fix's whole "
                  "point) 218 facts partition `train`, 201 `proved` and "
                  "exactly 17 `open` -- 5 outcome-blind mutation fixtures, 2 "
                  "divergence-blocked (`Nat.fastFib`, `Squarefree`), and the "
                  "10 `natural-binomial-bounds` rows (`Nat.choose_le_two_pow` "
                  "and siblings), none reachable by the bounded refl/"
                  "induction chain this producer runs. The producer "
                  "(`propose_bounded_induction`) was authored in "
                  "August against `natural-binomial-bounds`/factorial train "
                  "facts by a different lane and was not touched here -- the "
                  "property the rule protects (a producer tuned against the "
                  "evaluation set) does not hold. It cannot be repaired now "
                  "because every one of the four facts pins "
                  "`checker_operation.id` over this exact operation.",
    },
}


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


def manifest_paths() -> list[pathlib.Path]:
    """Every nursery manifest this gate reads, deduplicated and sorted.

    `NURSERY_DIR.glob` per `MANIFEST_GLOBS` pattern, not a single named file --
    see the comment on `MANIFEST_GLOBS` for the incident this replaced.
    """
    if not NURSERY_DIR.is_dir():
        return []
    return sorted({path for pattern in MANIFEST_GLOBS
                   for path in NURSERY_DIR.glob(pattern)})


def fact_partitions() -> dict[str, str]:
    """Partition per fact, from BOTH sources, requiring them to agree.

    The nursery records a `partition` on every entry AND the split policy
    records one per family. Measured 2026-08-22 the two agree on all 216 facts
    that have both (train 78, development 79, held-out 57), with `nat-bootstrap`
    carrying `longitudinal` and sitting outside the family policy by design.

    Two sources that can drift are a defect waiting to happen, and the drift
    would be silent: whichever file a reader consults would look authoritative.
    So disagreement is an ERROR here rather than a precedence rule -- picking a
    winner would hide exactly the edit that needs to be seen. The same rule now
    applies ACROSS manifests too: two nursery files naming the same fact id
    with different partitions is reported, never silently overwritten by
    whichever file happened to sort last.
    """
    manifests = manifest_paths()
    if not manifests:
        raise DevelopmentPartitionError(
            f"no nursery manifest matches {MANIFEST_GLOBS} under {NURSERY_DIR} "
            f"-- there is no drawn population to check"
        )
    policy = _load(SPLIT_POLICY)
    families = policy.get("family_partitions")
    if not isinstance(families, dict) or not families:
        raise DevelopmentPartitionError("split policy carries no family_partitions")

    out: dict[str, str] = {}
    declared_in: dict[str, str] = {}
    disagreements: list[str] = []
    for path in manifests:
        nursery = _load(path)
        entries = nursery.get("entries")
        if not isinstance(entries, list) or not entries:
            raise DevelopmentPartitionError(f"{path.name} carries no entries")
        for entry in entries:
            fact_id = entry.get("fact_id") or entry.get("id")
            partition = entry.get("partition")
            family = entry.get("family")
            if not fact_id or not partition:
                raise DevelopmentPartitionError(
                    f"{path.name} entry {fact_id or entry!r} carries no partition"
                )
            family_partition = families.get(family)
            if family_partition is not None and family_partition != partition:
                disagreements.append(
                    f"{fact_id}: entry says {partition!r}, family {family!r} says {family_partition!r}"
                )
            if fact_id in out and out[fact_id] != partition:
                disagreements.append(
                    f"{fact_id}: {partition!r} in {path.name} disagrees with "
                    f"{out[fact_id]!r} in {declared_in[fact_id]}"
                )
            out[fact_id] = partition
            declared_in[fact_id] = path.name
    if disagreements:
        raise DevelopmentPartitionError(
            "nursery manifests (or the nursery and split policy) disagree on "
            f"{len(disagreements)} fact(s): " + "; ".join(sorted(disagreements)[:5])
        )
    if not out:
        raise DevelopmentPartitionError("no nursery entry carried both a fact id and a partition")
    return out


def amended_fact_ids() -> set[str]:
    """Facts already spent by a recorded breach, and repaired by amendment.

    Reads `amendments` from EVERY manifest `manifest_paths()` finds, not just
    `nursery-v1.json` -- today only the v1 file carries any, but nothing in the
    schema confines them there, and a reader that assumed so would be the same
    defect this file just fixed for `entries`.
    """
    spent: set[str] = set()
    for path in manifest_paths():
        nursery = _load(path)
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


def operation_bindings() -> dict[str, set[str]]:
    """`{fact_id: {operation ids this fact pins in its own evidence}}`.

    Read from the SAME place `check-autogenesis-fact-operation.py` reads it
    (`evidence[*].checker_operation.id`), because the property being re-derived
    is that checker's: a fact whose evidence names an operation cannot have
    that operation edited or deleted without the evidence failing.
    """
    if not FACTS.is_dir():
        raise DevelopmentPartitionError("artifacts/facts is not a directory")
    out: dict[str, set[str]] = {}
    for path in sorted(FACTS.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise DevelopmentPartitionError(f"unreadable fact {path.name}: {exc}") from exc
        pinned: set[str] = set()
        for row in data.get("evidence") or []:
            binding = row.get("checker_operation") if isinstance(row, dict) else None
            if isinstance(binding, dict) and isinstance(binding.get("id"), str):
                pinned.add(binding["id"])
        out[data["id"]] = pinned
    return out


def grandfather_holds(
    op_id: str,
    touched_dev: set[str],
    statuses: dict[str, str],
    bindings: dict[str, set[str]],
) -> str | None:
    """Why this grandfather entry does NOT hold, or `None` when it does.

    Both properties are re-derived from the ledger. Neither is read off the
    entry, which carries prose and provenance only -- an exemption that
    believes its own reason is the mechanism ADR-1546 measured failing.
    """
    if op_id not in GRANDFATHERED_OPERATIONS:
        return f"{op_id} is not a grandfathered operation"
    unsettled = sorted(f for f in touched_dev if statuses.get(f) not in SETTLED)
    if unsettled:
        return (f"{op_id} is grandfathered but still covers OPEN development "
                f"fact(s) {unsettled} — a grandfather may not cover live "
                f"development work")
    unpinned = sorted(f for f in touched_dev if op_id not in bindings.get(f, set()))
    if unpinned:
        return (f"{op_id} is grandfathered on the ground that its targets pin "
                f"it, but {unpinned} do not name it in their evidence — so it "
                f"could be retired and must be, not excused")
    return None


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

    bindings = operation_bindings()
    violations: list[str] = []
    multi_target_facts: set[str] = set()
    grandfathers_used: set[str] = set()
    # Considered, not honoured: an entry whose properties were RE-DERIVED and
    # found false has been examined and reported, so it is not also stale.
    # Without this the same entry produces two violations and the stale check's
    # own control cannot be about the stale check.
    grandfathers_considered: set[str] = set()

    for operation in registry:
        op_id = operation.get("id", "<unnamed>")
        referenced = {s for s in _strings(operation) if s in partitions}
        touched_dev = {f for f in referenced if partitions[f] == "development"} - exempt
        touched_train = {f for f in referenced if partitions[f] == "train"}
        # `dev_only` is computed OUTSIDE the branch below on purpose. The
        # branch is a registered mutation target, and reading "was this entry
        # considered?" off the branch would make deleting the rule cascade into
        # every grandfather control -- a mutant that kills four tests says less
        # about the guard than one that kills the two whose subject it is.
        dev_only = bool(touched_dev) and not touched_train
        if dev_only and op_id in GRANDFATHERED_OPERATIONS:
            grandfathers_considered.add(op_id)
        if dev_only:
            # ADR-1563. The grandfather is checked, never asserted: a failing
            # entry falls through to the SAME violation the rule always
            # produced, and the reason it failed is printed with it.
            declined = grandfather_holds(op_id, touched_dev, statuses, bindings)
            if declined is None:
                grandfathers_used.add(op_id)
            else:
                violations.append(
                    f"{op_id} references development fact(s) {sorted(touched_dev)} "
                    f"and no train fact — a producer authored against the "
                    f"evaluation set [{declined}]"
                )
        fact_ids = operation.get("applicability", {}).get("fact_ids", [])
        if len(fact_ids) > 1:
            multi_target_facts.update(fact_ids)

    # A grandfather that fires on nothing is a violation, not a harmless
    # leftover: it is the stale-exemption failure this repository has already
    # paid for, and the only signal that the operation it names has changed
    # shape underneath the review that granted it.
    #
    # SCOPED TO OPERATIONS PRESENT IN THE REGISTRY BEING CHECKED. An entry
    # naming an operation this registry does not contain says nothing about
    # this registry -- and the control suite points the gate at synthetic
    # registries by design, so an unscoped check would report a finding about
    # a tree the entry was never about. That an entry names a LIVE operation is
    # a separate property with a separate control
    # (`LiveGrandfatherTests` in `scripts/tests/test_development_partition.py`,
    # which derives its subject from the committed registry rather than from a
    # list somebody kept in step).
    registry_ids = {operation.get("id") for operation in registry}
    for stale in sorted((set(GRANDFATHERED_OPERATIONS) & registry_ids)
                        - grandfathers_considered):
        violations.append(
            f"grandfathered operation {stale} matched no live violation — it "
            f"has changed shape or left the registry; delete the entry from "
            f"GRANDFATHERED_OPERATIONS rather than leaving an exemption that "
            f"suppresses nothing"
        )

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
            f"|grandfathered_operations={len(grandfathers_used)}"
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
