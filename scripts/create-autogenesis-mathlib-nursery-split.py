#!/usr/bin/env python3
"""Freeze the reviewed Mathlib facts into a preregistered leakage-safe nursery."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys
from collections import Counter
from typing import Any


ROOT = pathlib.Path(__file__).resolve().parents[1]
CATALOG = ROOT / "artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json"
POLICY = ROOT / "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"


class SplitError(RuntimeError):
    """The preregistered split cannot be reproduced exactly."""


PREREGISTERED_STATES = {
    "preregistered-before-target-outcomes",
    "preregistered-before-target-outcomes-with-recorded-amendments",
}
# Held-out shrinks only, and only through the ADR-0542 amendment ledger. The
# arithmetic is the audit trail: 76 at preregistration, -19 natural-gcd
# (2026-08-22), -20 natural-binomial (2026-08-25), -21 natural-logarithm
# (2026-08-30) = 16, the natural-square-root family alone.
PARTITION_COUNTS = {"train": 78, "development": 120, "held-out": 16}
AMENDMENT_KEYS = {
    "date", "family", "from", "to", "reason", "breach", "authority", "irreversible",
}
BREACH_KEYS = {
    "fact_id", "proof_shape", "operation_id", "registered_commit",
    "registered_date", "detected_date",
}

# WHICH PARTITIONS ARE EVALUATED, AND WHICH ONE IS FOR TRAINING (ADR-1564).
#
# This used to be a literal three-element list inside `build`, copied verbatim
# into every gate that read it. It is now carried from the split policy's
# `partition_roles` block, because it is a PREREGISTERED decision about what
# the split protects and the gates that enforce it must derive it from one
# authority rather than each hold their own copy -- CLAUDE.md's rule that a
# check named "every X" must read its X from the authority, not from the
# maintainer's memory of it.
#
# `PREREGISTERED_PARTITION_ROLES` is the shape the split was FROZEN with on
# 2026-08-18. It is not the shape that ships today; it is what a departure is
# measured against, so that changing the roles requires a dated
# `policy_amendments` entry and cannot be an edit in place. See
# `validate_partition_roles`.
PARTITION_ROLE_KEYS = {
    "required_evaluation_partitions", "training_partitions",
    "blind_partitions", "crossing_rule",
}
POLICY_AMENDMENT_KEYS = {
    "date", "authority", "change", "reason", "does_not_change", "irreversible",
}
PREREGISTERED_PARTITION_ROLES = {
    "required_evaluation_partitions": ["train", "development", "held-out"],
    "training_partitions": [],
    "blind_partitions": ["held-out"],
}


def validate_partition_roles(split_policy: dict[str, Any]) -> dict[str, Any]:
    """The three role lists, and the dated amendment any departure needs.

    THE POINT OF THE AMENDMENT REQUIREMENT. The split policy is frozen
    `before-target-outcomes`; the partitions it evaluates are part of what was
    frozen. Editing that list in place would be indistinguishable from having
    always meant it, which is the exact failure mode ADR-1546 measured on the
    component exemption that was re-scoped 228 -> 230 -> 258 -> 274 to fit
    whatever it had just failed on. So a `partition_roles` block that differs
    from `PREREGISTERED_PARTITION_ROLES` in ANY of the three lists must be
    accompanied by at least one `policy_amendments` entry -- dated, with an
    authority and a stated change.

    Two structural rules the roles themselves must satisfy, both of which are
    the reason `blind_partitions` exists as its own list rather than being
    inferred from the evaluation list:

      * a training partition is never also an evaluation partition, or the
        role says nothing; and
      * `blind_partitions` is a NON-EMPTY subset of the evaluation partitions.
        A policy that seals nothing would make a training partition's edges to
        the blind population ordinary, and held-out blindness once spent
        cannot be un-spent. This validator is where that is refused, so the
        seal is not something a producer can drop by editing data.
    """
    roles = split_policy.get("partition_roles")
    if not isinstance(roles, dict) or set(roles) != PARTITION_ROLE_KEYS:
        raise SplitError(
            f"split policy partition_roles must be an object with exactly "
            f"{sorted(PARTITION_ROLE_KEYS)}")
    lists: dict[str, list[str]] = {}
    for key in ("required_evaluation_partitions", "training_partitions",
                "blind_partitions"):
        value = roles[key]
        if not isinstance(value, list) or not all(
            isinstance(item, str) and item for item in value
        ):
            raise SplitError(f"partition_roles.{key} must be a list of strings")
        if len(set(value)) != len(value):
            raise SplitError(f"partition_roles.{key} repeats a partition")
        lists[key] = value
    if not lists["required_evaluation_partitions"]:
        raise SplitError(
            "partition_roles.required_evaluation_partitions is empty: a split "
            "that evaluates nothing is not a split")
    overlap = sorted(set(lists["training_partitions"])
                     & set(lists["required_evaluation_partitions"]))
    if overlap:
        raise SplitError(
            f"partition_roles: {overlap} is both a training and an evaluation "
            f"partition, which is not a role")
    if not lists["blind_partitions"]:
        raise SplitError(
            "partition_roles.blind_partitions is empty: the blind population "
            "is what the split exists to protect and it is not optional")
    stray = sorted(set(lists["blind_partitions"])
                   - set(lists["required_evaluation_partitions"]))
    if stray:
        raise SplitError(
            f"partition_roles.blind_partitions names {stray}, which is not an "
            f"evaluation partition")
    if not isinstance(roles["crossing_rule"], str) or not roles["crossing_rule"]:
        raise SplitError("partition_roles.crossing_rule must say what a crossing is")

    amendments = split_policy.get("policy_amendments", [])
    if not isinstance(amendments, list):
        raise SplitError("split policy policy_amendments must be a list")
    for amendment in amendments:
        if not isinstance(amendment, dict) or set(amendment) != POLICY_AMENDMENT_KEYS:
            raise SplitError(
                f"policy amendment fields differ: {sorted(amendment)}")
        for key in ("date", "authority", "change", "reason"):
            if not isinstance(amendment[key], str) or not amendment[key]:
                raise SplitError(f"policy amendment {key} must be a nonempty string")
    departed = any(lists[key] != PREREGISTERED_PARTITION_ROLES[key]
                   for key in PREREGISTERED_PARTITION_ROLES)
    if departed and not amendments:
        raise SplitError(
            "partition_roles departs from the preregistered roles "
            f"{PREREGISTERED_PARTITION_ROLES} with no policy_amendments entry: "
            "the evaluated partitions are part of what was frozen "
            "before-target-outcomes, so a change to them is an AMENDMENT with "
            "a date and an authority, never an edit in place")
    if amendments and not departed:
        raise SplitError(
            "policy_amendments are recorded but partition_roles is still the "
            "preregistered shape: an amendment that changes nothing is a "
            "claim nobody can check")
    return lists


def validate_amendments(split_policy: dict[str, Any]) -> list[dict[str, Any]]:
    """A partition amendment is a spend of evaluation value; it must be legible.

    An amendment that omitted its breach would be indistinguishable from an
    ordinary edit to the split, which is the failure this ledger exists to make
    impossible.
    """
    amendments = split_policy.get("amendments", [])
    if not isinstance(amendments, list):
        raise SplitError("split policy amendments must be a list")
    if amendments and split_policy["state"] != (
        "preregistered-before-target-outcomes-with-recorded-amendments"
    ):
        raise SplitError("amendments are present but the policy state does not say so")
    if not amendments and split_policy["state"] != (
        "preregistered-before-target-outcomes"
    ):
        raise SplitError("the policy state claims amendments but none are recorded")
    for amendment in amendments:
        if not isinstance(amendment, dict) or set(amendment) != AMENDMENT_KEYS:
            raise SplitError(f"amendment fields differ: {sorted(amendment)}")
        if amendment["from"] != "held-out":
            raise SplitError("only a held-out spend needs an amendment record")
        if amendment["irreversible"] is not True:
            raise SplitError("a held-out spend is not reversible")
        breach = amendment["breach"]
        if not isinstance(breach, dict) or set(breach) != BREACH_KEYS:
            raise SplitError(f"amendment breach fields differ: {sorted(breach)}")
        if not all(isinstance(v, str) and v for v in breach.values()):
            raise SplitError("amendment breach fields must be nonempty strings")
    return amendments


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def load(path: pathlib.Path) -> dict[str, Any]:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise SplitError(f"{path.relative_to(ROOT)} is not an object")
    return value


def build(catalog: dict[str, Any], split_policy: dict[str, Any]) -> dict[str, Any]:
    if catalog.get("state") != "open-facts-no-splits-no-outcomes":
        raise SplitError("fact catalog state is invalid")
    unsigned = dict(catalog)
    claimed = unsigned.pop("catalog_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise SplitError("fact catalog digest is invalid")
    if split_policy.get("state") not in PREREGISTERED_STATES:
        raise SplitError("split policy is not preregistered")
    amendments = validate_amendments(split_policy)
    roles = validate_partition_roles(split_policy)
    family_partitions = split_policy.get("family_partitions")
    route_hypotheses = split_policy.get("route_hypotheses")
    if not isinstance(family_partitions, dict) or not isinstance(route_hypotheses, dict):
        raise SplitError("split policy mappings are invalid")
    rows = catalog.get("facts")
    if not isinstance(rows, list) or len(rows) != 214:
        raise SplitError("fact catalog must contain the reviewed 214-row population")
    families = {row.get("family") for row in rows}
    if families != set(family_partitions) or families != set(route_hypotheses):
        raise SplitError("split policy does not cover the catalog families exactly")

    entries = [
        {
            "fact_id": "F:nat-zero-add",
            "partition": "longitudinal",
            "provenance_class": "project-constructed",
            "family": "nat-bootstrap",
            "proof_shape": "kernel-induction",
            "source_group": "autogenesis-1",
            "route_hypotheses": ["kernel-induction"],
            "mutation_of": None,
            "answer_access": "withheld-during-episode",
        },
        {
            "fact_id": "F:nat-mul-one",
            "partition": "longitudinal",
            "provenance_class": "project-constructed",
            "family": "nat-bootstrap",
            "proof_shape": "kernel-theorem-application",
            "source_group": "autogenesis-1",
            "route_hypotheses": ["kernel-library-application"],
            "mutation_of": None,
            "answer_access": "withheld-during-episode",
        },
    ]
    for row in sorted(rows, key=lambda item: item["fact_id"]):
        family = row["family"]
        routes = route_hypotheses[family]
        if routes != sorted(set(routes)):
            raise SplitError(f"route hypotheses for {family} are not sorted and unique")
        generated = row["kind"] == "generated-mutation"
        entries.append(
            {
                "fact_id": row["fact_id"],
                "partition": family_partitions[family],
                "provenance_class": "generated-mutation" if generated else "external-transcribed",
                "family": family,
                "proof_shape": f"{family}:{row['statement_shape']}",
                "source_group": row["dependency_component_id"],
                "route_hypotheses": routes,
                "mutation_of": row.get("mutation_of_fact_id"),
                "answer_access": "unavailable" if generated else "withheld-during-episode",
            }
        )
    for amendment in amendments:
        family = amendment["family"]
        if family_partitions.get(family) == "held-out":
            raise SplitError(
                f"amended family {family!r} is assigned to held-out; a family whose "
                "blind-evaluation value was spent cannot be recycled into held-out"
            )
    counts = Counter(entry["partition"] for entry in entries[2:])
    if counts != PARTITION_COUNTS:
        raise SplitError(f"preregistered partition counts changed: {dict(counts)}")
    return {
        "schema_version": 1,
        "kind": "axeyum-autogenesis-nursery",
        "state": "frozen-evaluation",
        "policy": {
            "admission_dependency_authority": "proof-derived-kernel-dependency",
            "evaluation_fact_count": {"maximum": 300, "minimum": 100},
            "minimum_declared_dependency_depth": 2,
            "minimum_held_out_components": 1,
            "minimum_provenance_classes": 2,
            "minimum_route_hypothesis_families": 2,
            "minimum_statement_mutations": 1,
            "family_leakage": "no-family-may-cross-evaluation-partitions",
            "proof_shape_leakage": "no-proof-shape-may-cross-evaluation-partitions",
            "source_group_leakage": "no-source-review-group-may-cross-evaluation-partitions",
            "required_evaluation_partitions": roles["required_evaluation_partitions"],
            "training_partitions": roles["training_partitions"],
            "blind_partitions": roles["blind_partitions"],
            "split_component_authority": "declared-dependency-weak-component",
            "split_freeze": "before-target-outcomes",
            "split_leakage": "no-declared-component-may-cross-evaluation-partitions",
        },
        "amendments": amendments,
        "entries": entries,
        "longitudinal_result": "artifacts/autogenesis/autogenesis-1-result.json",
        "split_policy": "artifacts/autogenesis/mathlib-nursery-split-policy-v1.json",
        "split_policy_sha256": digest(split_policy),
        "source_catalog_sha256": catalog["catalog_sha256"],
        "notes": "Autogenesis-1 remains a disjoint longitudinal regression. The 214 Mathlib statements are frozen before target outcomes; source groups, families, family-scoped proof shapes, mutations, and declared dependency components cannot cross evaluation partitions.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        expected = build(load(CATALOG), load(POLICY))
        rendered = json.dumps(expected, indent=2, ensure_ascii=False) + "\n"
        if args.check:
            if not NURSERY.exists() or NURSERY.read_text() != rendered:
                raise SplitError("nursery-v1.json is stale; regenerate without --check")
        else:
            NURSERY.write_text(rendered)
        print(
            "AUTOGENESIS_MATHLIB_NURSERY_SPLIT_OK|"
            f"{digest(expected)}|evaluation={len(expected['entries']) - 2}|"
            + "|".join(f"{k}={v}" for k, v in sorted(PARTITION_COUNTS.items()))
            + f"|amendments={len(expected['amendments'])}"
        )
    except (OSError, json.JSONDecodeError, KeyError, SplitError) as error:
        print(f"autogenesis-mathlib-nursery-split: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
