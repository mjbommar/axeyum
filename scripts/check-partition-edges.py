#!/usr/bin/env python3
"""Every `depends_on` edge that crosses an evaluation partition is a violation.

WHY THIS EXISTS (ADR-1546 option 2, recorded as taken in ADR-1550).

`check-autogenesis-nursery.py` enforces
`split_leakage: no-declared-component-may-cross-evaluation-partitions` over
the WEAK COMPONENTS of the declared-dependency graph. It is right about its
subject and it is the wrong instrument for a producer, for two measured
reasons:

  1. IT RUNS IN NO PRE-PUSH GATE. `hooks/pre-push` ran
     `check-settled-fact-statements.py` and `check-holdout-closed-evaluation.py`
     and neither nursery gate, so a producer could close a fact whose
     `depends_on` fuses two evaluation partitions and push it without the
     property ever being evaluated. Both crossing edges of 2026-09-01 landed
     that way.
  2. A COMPONENT IS THE WRONG UNIT TO EXEMPT. A component grows when any
     member gains an edge, so an exemption that names a component's fact-id
     SET goes stale on the next producer commit and the only cheap repair is
     to enlarge it. Measured in ADR-1546: 228 -> 230 -> 258 -> 274 members in
     four days, against a live component of 305. A gate whose largest subject
     is waved through by an exemption enlarged to fit whenever it fails cannot
     fail on that subject, which is the failure mode CLAUDE.md names.

So this gate changes the unit. THE SUBJECT IS ONE EDGE: a `depends_on` entry
in one fact naming another fact, where the two facts sit in different
evaluation partitions. One edge is what a producer actually adds, it is
attributable to one commit by a pickaxe search, and -- unlike a component --
it never changes shape underneath the person who reviewed it. An exemption
here must therefore name ONE EDGE, a reason and a date; anything else is
refused.

WHAT IS AND IS NOT HONOURED

  * `artifacts/autogenesis/partition-edge-amendments-v1.json` -- a list whose
    every element names `from`, `to`, `reason`, `date`. Honoured per edge.
  * `cross_population_component_split_exemptions` (and
    `component_split_exemptions`) in the nursery manifests -- NOT honoured,
    and reported as `NOT-AN-AMENDMENT`. They name a fact-id SET, which is a
    count-shaped exemption for this gate's purpose: nothing in one of them
    says which edge was reviewed, so honouring it would suppress an edge
    nobody looked at. That is not a criticism of what those entries do for
    `check-autogenesis-nursery.py`, whose unit is the component; it is a
    statement that they are unparseable AS PER-EDGE AMENDMENTS.

THE RATCHET (`--baseline`)

The existing crossings are not this gate's to repair -- re-partitioning is
ADR-1546 option 1 and belongs to the draw. So `--record-baseline` freezes
today's crossing edge set into
`artifacts/autogenesis/partition-edge-baseline-v1.json` and `--baseline` fails
only on edges NOT in it. New crossings are blocked from today; the recorded
ones are repaired by the re-partition. `--record-baseline` REFUSES to record a
set that is not a subset of the committed baseline, so the ratchet can only
tighten: a lane cannot silence a new crossing by re-recording.

HELD-OUT ENDPOINTS ARE NEVER WRITTEN IN PLAIN TEXT

The recorded baseline is a committed, producer-readable artifact, and
`scripts/check-autogenesis-holdout-isolation.py` treats a held-out fact id
appearing anywhere outside the split manifests as a breach -- which the first
version of this baseline was, for the six of 198 crossings with a held-out
endpoint. So a `held-out`-partition endpoint is stored as a salted SHA-256
digest (`held_out_endpoint: true`), with the salt committed alongside it
(`held_out_salt`); every other endpoint stays plain. `--baseline` digests a
live crossing edge's held-out endpoint with the committed salt before testing
membership, and `--record-baseline` reuses that salt whenever the edge set is
unchanged, so an unperturbed re-record is still byte-identical. See
`redacted_key`'s docstring for the mechanism.

EXITS
  0  no violation (or, under --baseline, no violation outside the baseline)
  1  at least one violation
  2  cannot answer -- no manifests, no fact ledger, or --baseline with no
     baseline file. Deliberately distinct from 1: a gate that reports a
     disagreement when its subject was unavailable is wrong about its own
     subject.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import pathlib
import secrets
import subprocess
import sys
from typing import Any

# `AXEYUM_PARTITION_EDGES_ROOT` points the SHIPPED script at a throwaway tree
# so `scripts/tests/test_check_partition_edges.py` can drive every guard to
# failure without re-implementing it and without dirtying the real checkout.
# Same device as `AXEYUM_MERGE_HYGIENE_ROOT` and `AXEYUM_KERNEL_SUITES_ROOT`.
DEFAULT_ROOT = pathlib.Path(__file__).resolve().parents[1]

# NOT a single wide `nursery*.json` glob. That shape went UNANSWERABLE
# (`Unanswerable`, exit 2) the moment ANY unrelated file matching it landed in
# `artifacts/autogenesis/` -- `load_partitions` treats every glob hit as a
# manifest and raises the instant one lacks a usable `entries` list, so a
# committed decoy like `nursery-zzz-notes.json` takes this gate down with no
# relation to a real crossing. Two explicit patterns name exactly what a
# manifest here IS: the v1 split (`nursery-v1.json`) and a refill extension
# (`nursery-v*-extension.json`, so a future `nursery-v3-extension.json` is
# still found without widening this file again). Neither matches a decoy
# named anything else, which is the property `test_a_decoy_nursery_file_does_
# not_make_this_gate_unanswerable` in the control suite pins.
MANIFEST_GLOBS = ("artifacts/autogenesis/nursery-v1.json",
                  "artifacts/autogenesis/nursery-v*-extension.json")
FACTS_DIR = "artifacts/facts"
BASELINE_PATH = "artifacts/autogenesis/partition-edge-baseline-v1.json"
AMENDMENTS_PATH = "artifacts/autogenesis/partition-edge-amendments-v1.json"

# Every partition an entry may declare. `longitudinal` is in here on purpose:
# ADR-1546 counted the 305-member component across development / train /
# held-out / longitudinal, and an edge from a drawn evaluation fact into the
# longitudinal regression population is the same leak wearing a different
# name.
PARTITIONS = ("longitudinal", "train", "development", "held-out")

# The three role lists this gate reads out of a manifest's `policy` block, and
# what each one does to the crossing rule. See `load_policy` and
# `PartitionRoles.is_crossing`.
POLICY_ROLE_KEYS = ("required_evaluation_partitions", "training_partitions",
                    "blind_partitions")

# The exemption keys this gate refuses to read as amendments. Named, not
# pattern-matched, so the report says WHICH construct was declined.
COUNT_STYLE_EXEMPTION_KEYS = (
    "cross_population_component_split_exemptions",
    "component_split_exemptions",
)

# The amendment classes this gate re-derives (ADR-1563). A class is not a
# label an author asserts; it is a property `class_complaint` recomputes from
# the live manifests, and an amendment whose class does not hold is refused.
# Adding a name here without a matching arm in `class_complaint` would make it
# a label again, which is why the membership test and the arms live in one
# function.
AMENDMENT_CLASSES = ("depends-on-longitudinal-bootstrap",
                     "scored-evaluation-residue")

# The evaluation records `scored-evaluation-residue` is keyed to (ADR-1566).
# An amendment in that class names a `record_id` FROM THIS FILE and never a
# fact id: a record is a committed artifact with a preregistration commit in
# it, so every clause of the class is a claim about this file and the commit
# graph rather than a judgement about a row.
EVALUATION_RECORDS_PATH = "artifacts/autogenesis/holdout-evaluation-v1.json"


class Unanswerable(RuntimeError):
    """The gate could not evaluate its subject. Exit 2, never 1."""


def sha256_of(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise Unanswerable(f"{path}: unreadable ({exc})") from exc


def manifest_paths(root: pathlib.Path) -> list[pathlib.Path]:
    """Every path any `MANIFEST_GLOBS` pattern matches, deduplicated and sorted.

    A `set` first: `nursery-v1.json` cannot also match the extension pattern
    today, but nothing enforces that two patterns here stay disjoint forever,
    and a duplicate manifest counted twice would double its fact ids in
    `load_partitions`' loop.
    """
    return sorted({path for pattern in MANIFEST_GLOBS
                   for path in root.glob(pattern)})


# --------------------------------------------------------------------------
# The subject
# --------------------------------------------------------------------------

def load_partitions(root: pathlib.Path) -> tuple[dict[str, str], list[str]]:
    """`{fact_id: partition}` over every nursery manifest, plus their paths."""
    manifests = manifest_paths(root)
    if not manifests:
        raise Unanswerable(
            f"no nursery manifest matches {MANIFEST_GLOBS} under {root} -- "
            f"there is no drawn population to check, which is not the same "
            f"as a clean one")
    partition_of: dict[str, str] = {}
    declared_in: dict[str, str] = {}
    names: list[str] = []
    for path in manifests:
        rel = str(path.relative_to(root))
        names.append(rel)
        document = load_json(path)
        if not isinstance(document, dict):
            raise Unanswerable(f"{rel}: not a JSON object")
        entries = document.get("entries")
        if not isinstance(entries, list):
            raise Unanswerable(f"{rel}: entries is not a list")
        for index, entry in enumerate(entries):
            if not isinstance(entry, dict):
                raise Unanswerable(f"{rel}: entries[{index}] is not an object")
            fact_id = entry.get("fact_id")
            partition = entry.get("partition")
            if not isinstance(fact_id, str) or partition not in PARTITIONS:
                raise Unanswerable(
                    f"{rel}: entries[{index}] has no usable fact_id/partition")
            if fact_id in partition_of and partition_of[fact_id] != partition:
                raise Unanswerable(
                    f"{fact_id} is {partition_of[fact_id]} in "
                    f"{declared_in[fact_id]} and {partition} in {rel}")
            partition_of[fact_id] = partition
            declared_in[fact_id] = rel
    return partition_of, names


def load_dependencies(root: pathlib.Path) -> dict[str, tuple[list[str], str]]:
    """`{fact_id: (depends_on, path relative to root)}` over the fact ledger."""
    facts_dir = root / FACTS_DIR
    if not facts_dir.is_dir():
        raise Unanswerable(f"{FACTS_DIR} is absent under {root}")
    out: dict[str, tuple[list[str], str]] = {}
    for path in sorted(facts_dir.glob("*.json")):
        fact = load_json(path)
        if not isinstance(fact, dict):
            continue
        fact_id = fact.get("id")
        if not isinstance(fact_id, str):
            continue
        depends_on = fact.get("depends_on") or []
        if not isinstance(depends_on, list):
            raise Unanswerable(f"{path.name}: depends_on is not a list")
        out[fact_id] = ([d for d in depends_on if isinstance(d, str)],
                        str(path.relative_to(root)))
    return out


class PartitionRoles:
    """Which partitions are evaluated, which train, and which are blind.

    ADR-1564. This gate used to treat EVERY pair of distinct partitions as a
    crossing, which was right while `required_evaluation_partitions` was
    `[train, development, held-out]` and is wrong now that it is
    `[development, held-out]`. The roles are READ FROM THE POLICY (see
    `load_policy`), never spelled here: a literal would be a second copy of a
    preregistered decision, and the whole reason ADR-1563 could not amend the
    147 dev<->train edges was that the gate's literal and the manifest's list
    said the same wrong thing to each other.

    THE RULE, and why `blind` is its own list rather than something inferred.
    A `depends_on` edge is a crossing unless it joins a TRAINING partition to a
    NON-BLIND evaluation partition, in either direction. Training is what a
    producer is allowed to build on, so `development -> train` (a development
    row citing a proved train lemma) and `train -> development` are both fine
    -- that is what a training set is for. A BLIND partition is sealed in both
    directions whatever the other endpoint's role: `train -> held-out` spends
    blindness exactly as `development -> held-out` does, and `held-out -> X`
    entangles a blind row with a population producers work on. Blindness once
    spent cannot be un-spent, so it is not a role that trades against
    convenience, and `load_policy` REFUSES a policy that seals nothing.
    """

    def __init__(self, evaluation: set[str], training: set[str],
                 blind: set[str]) -> None:
        self.evaluation = evaluation
        self.training = training
        self.blind = blind

    def is_crossing(self, source: str, target: str) -> bool:
        if source == target:
            return False
        peers = {source, target} - self.training
        if len(peers) != 1:
            # No training endpoint (so nothing licenses the pair), or BOTH
            # endpoints training (so there is no evaluation partition here to
            # protect and the pair is not this gate's subject either way --
            # `len(peers) != 1` covers both, and the second case cannot occur
            # while one partition trains).
            return len(peers) == 2
        peer = next(iter(peers))
        if peer in self.blind:
            # A BLIND partition is sealed in BOTH directions, training peer or
            # not. `train -> held-out` spends blindness exactly as
            # `development -> held-out` does.
            return True
        return peer not in self.evaluation

    def summary(self) -> str:
        return (f"evaluation={'+'.join(sorted(self.evaluation))}"
                f"|training={'+'.join(sorted(self.training)) or 'none'}"
                f"|blind={'+'.join(sorted(self.blind))}")


def load_policy(root: pathlib.Path) -> PartitionRoles:
    """The partition roles, read from the manifests' own `policy` block.

    Exactly one manifest may carry a `policy`; today that is
    `nursery-v1.json`, and `nursery-v*-extension.json` declares `extends` and
    inherits it. TWO disagreeing policies is `Unanswerable`, not a choice: a
    gate that picks one of two authorities is reporting on a tree that does not
    exist.

    A POLICY NAMING NO EVALUATION PARTITION IS EXIT 2, NOT A CLEAN TREE. With
    an empty evaluation set every edge would be permitted and this gate would
    print `crossing=0 ... PASS` over a ledger it never judged -- the shape
    CLAUDE.md names, a checker that cannot fail. Same for an empty
    `blind_partitions`: it would silently unseal the held-out population, which
    is the one thing here that cannot be undone.
    """
    found: list[tuple[str, dict[str, Any]]] = []
    for path in manifest_paths(root):
        document = load_json(path)
        if isinstance(document, dict) and "policy" in document:
            policy = document["policy"]
            if not isinstance(policy, dict):
                raise Unanswerable(
                    f"{path.relative_to(root)}: policy is not an object")
            found.append((str(path.relative_to(root)), policy))
    if not found:
        raise Unanswerable(
            "no nursery manifest carries a `policy` block, so which "
            "partitions are evaluated is unknown -- that is not the same as "
            "nothing crossing")
    roles: list[str] = []
    for name, policy in found:
        values = {key: policy.get(key) for key in POLICY_ROLE_KEYS}
        for key, value in values.items():
            if not isinstance(value, list) or any(
                item not in PARTITIONS for item in value
            ):
                raise Unanswerable(
                    f"{name}: policy.{key} must be a list drawn from "
                    f"{list(PARTITIONS)}")
        roles.append(json.dumps(values, sort_keys=True))
    if len(set(roles)) != 1:
        raise Unanswerable(
            "the nursery manifests disagree about the partition roles: "
            + "; ".join(f"{name} says {role}"
                        for (name, _), role in zip(found, roles)))
    values = json.loads(roles[0])
    evaluation = set(values["required_evaluation_partitions"])
    training = set(values["training_partitions"])
    blind = set(values["blind_partitions"])
    if not evaluation:
        raise Unanswerable(
            "policy.required_evaluation_partitions is empty: with nothing "
            "evaluated every edge is permitted and this gate would pass over "
            "a ledger it never judged")
    if training & evaluation:
        raise Unanswerable(
            f"policy: {sorted(training & evaluation)} is both a training and "
            f"an evaluation partition, which is not a role")
    if not blind or blind - evaluation:
        raise Unanswerable(
            "policy.blind_partitions must be a non-empty subset of "
            "required_evaluation_partitions: blindness once spent cannot be "
            "un-spent, so the seal is not optional")
    return PartitionRoles(evaluation, training, blind)


def crossing_edges(
    partition_of: dict[str, str],
    dependencies: dict[str, tuple[list[str], str]],
    roles: PartitionRoles,
) -> list[dict[str, str]]:
    """Every DIRECTED `depends_on` edge that CROSSES, per `roles`.

    Directed, not collapsed to an unordered pair, because the directed edge is
    what a producer writes: it is one string in one fact file, and it is what
    the pickaxe search attributes to a commit. `a depends_on b` and
    `b depends_on a` are two separate things somebody did.
    """
    edges: list[dict[str, str]] = []
    for fact_id, source_partition in sorted(partition_of.items()):
        depends_on, source_path = dependencies.get(fact_id, ([], ""))
        for dependency in depends_on:
            target_partition = partition_of.get(dependency)
            if target_partition is None or not roles.is_crossing(
                source_partition, target_partition
            ):
                continue
            edges.append({
                "from": fact_id,
                "from_partition": source_partition,
                "to": dependency,
                "to_partition": target_partition,
                "declared_in": source_path,
            })
    edges.sort(key=lambda e: (e["from"], e["to"]))
    return edges


def edge_key(edge: dict[str, str]) -> tuple[str, str]:
    return (edge["from"], edge["to"])


# --------------------------------------------------------------------------
# Held-out redaction -- the BASELINE ARTIFACT never carries a held-out fact id
# in plain text.
#
# WHY. `partition-edge-baseline-v1.json` is a committed, producer-readable
# artifact, and `check-autogenesis-holdout-isolation.py` treats a held-out id
# appearing anywhere in the tree (outside the split manifests themselves) as a
# breach -- ADR-1550's own baseline was six such breaches, because the first
# version stored every crossing edge's endpoints as plain fact ids regardless
# of partition. A held-out id existing in this file at all is not the
# violation (the manifests that DEFINE the population already name it); the
# violation is a PRODUCER being able to read it, which is exactly what a
# committed JSON artifact offers to any script or model that opens it.
#
# So an endpoint whose partition is `held-out` is stored as a salted SHA-256
# digest instead of the fact id, with `held_out_endpoint: true` alongside it.
# The salt lives in the same file (`held_out_salt`) -- committing the salt
# next to the digest does not make the digest reversible, and a reader who
# already has the plain id can still confirm it produced this digest, which is
# what a re-derivation audit needs. What nobody gets from this file is the id
# itself, and a `grep` for it finds nothing here.
#
# The salt is CARRIED FORWARD whenever the edge set does not change (mirrors
# `recorded_date`/`recorded_at_commit`/`ledger_sha256` in `render_baseline`):
# regenerating a byte-identical file from an unperturbed edge set must produce
# the identical digest, or `check-generated-artifact-ownership.py`'s OWNER arm
# -- which perturbs a copy and demands the owner restore it byte-for-byte --
# cannot pass.
def digest_fact_id(fact_id: str, salt: str) -> str:
    return hashlib.sha256(f"{salt}:{fact_id}".encode()).hexdigest()


def resolve_salt(previous: dict[str, Any] | None) -> str:
    """Reuse the committed salt, or mint a fresh one when there is none yet.

    A fresh salt only when `previous` has none -- never on every run -- is
    what keeps an unchanged edge set's digests unchanged (see module note
    above). `secrets.token_hex`, not `hashlib` over something guessable: this
    salt is the only thing standing between a digest and a dictionary attack
    over ~200 known-shape `F:ml430-...` ids, so it must not be derivable from
    public state.
    """
    if previous is not None:
        salt = previous.get("held_out_salt")
        if isinstance(salt, str) and salt:
            return salt
    return secrets.token_hex(32)


def redacted_key(edge: dict[str, str], salt: str | None) -> tuple[str, str]:
    """The edge's `(from, to)` pair AS IT APPEARS IN THE BASELINE FILE.

    A held-out endpoint (`from_partition`/`to_partition` == `held-out`) is
    digested; the other endpoint, and every endpoint of a non-held-out edge,
    stays plain. `salt is None` degrades to the fully-plain pair rather than
    raising -- a baseline recorded before this change, or a test fixture that
    never declares a held-out partition, has no salt and no digested endpoint
    to match, so there is nothing to redact and comparing plain-to-plain is
    exactly correct.

    THIS is `--baseline`'s half of "digest the live id the same way before
    comparing": every membership test against a committed baseline's key set
    must call this, never bare `edge_key`, or a live held-out crossing can
    never be recognised as already-baselined and the ratchet would fail
    closed on every push.
    """
    frm = (digest_fact_id(edge["from"], salt)
           if salt and edge["from_partition"] == "held-out" else edge["from"])
    to = (digest_fact_id(edge["to"], salt)
          if salt and edge["to_partition"] == "held-out" else edge["to"])
    return (frm, to)


def redacted_row(edge: dict[str, str], salt: str) -> dict[str, Any]:
    """One row of the committed baseline, with any held-out endpoint digested."""
    frm, to = redacted_key(edge, salt)
    row: dict[str, Any] = {
        "from": frm, "from_partition": edge["from_partition"],
        "to": to, "to_partition": edge["to_partition"],
    }
    if edge["from_partition"] == "held-out" or edge["to_partition"] == "held-out":
        row["held_out_endpoint"] = True
    return row


def committed_salt(root: pathlib.Path) -> str | None:
    """The salt the COMMITTED baseline records, or `None` when there is none.

    Distinct from `resolve_salt`, which MINTS one when a baseline has none --
    exactly the wrong behaviour for matching, because a fresh salt would digest
    a live id into something no committed artifact contains, and every
    redaction-keyed amendment would silently stop matching. This one never
    invents a salt: no baseline, no salt, and `edge_is_amended` then compares
    plain-to-plain, which is right for a fixture tree that has no held-out
    endpoint to redact in the first place.
    """
    path = root / BASELINE_PATH
    if not path.is_file():
        return None
    try:
        document = load_json(path)
    except Unanswerable:
        return None
    if not isinstance(document, dict):
        return None
    salt = document.get("held_out_salt")
    return salt if isinstance(salt, str) and salt else None


def edge_is_amended(edge: dict[str, str], amendments: set[tuple[str, str]],
                    salt: str | None) -> bool:
    """Is this DIRECTED edge covered by the amendment set, in either form?

    ADR-1566. An amendment may name its endpoints plainly, or -- when an
    endpoint is blind -- in the SAME salted-digest form the baseline stores
    (`redacted_key`). Both are one edge; which representation an author had to
    use is a property of the endpoint's partition, not of the decision.

    THIS IS THE ONLY PLACE THAT RULE LIVES. `check-autogenesis-nursery.py`
    calls it rather than re-deriving the comparison, for the same reason it
    loads `load_amendments` by path: two gates that disagree about which edge an
    amendment covers is a pair of reports describing no tree at all.
    """
    return (edge_key(edge) in amendments
            or redacted_key(edge, salt) in amendments)


# --------------------------------------------------------------------------
# Amendments -- per edge, or not at all
# --------------------------------------------------------------------------

class ClassContext:
    """Everything an amendment CLASS is re-derived from, loaded on demand.

    ADR-1566. `depends-on-longitudinal-bootstrap` needs only the partition map,
    which `load_amendments` already has. `scored-evaluation-residue` needs four
    more things -- the drawn population's FAMILY column, the committed
    evaluation records, the policy's `blind_partitions`, and the commit graph --
    and every one of them can be absent in a tree that has no such amendment
    (the control suites' fixture trees carry no policy block and no records
    file).

    So the loading is LAZY and per-property, and a failure to load is a
    COMPLAINT about the amendment that asked for it, never a crash and never a
    silent pass. An amendment whose class cannot be re-derived is not honoured,
    which is the same treatment a missing field gets: the one thing that must
    not happen is a class going unchecked because the evidence for it was
    unavailable.
    """

    def __init__(self, root: pathlib.Path,
                 partition_of: dict[str, str]) -> None:
        self.root = root
        self.partition_of = partition_of
        self._families: dict[str, str] | None = None
        self._records: dict[str, dict[str, Any]] | None = None
        self._blind: set[str] | None = None
        self._digests: dict[str, str] | None = None
        self._paths: dict[str, str] | None = None
        self._git_available: bool | None = None
        # Clauses that could NOT be re-derived because the evidence for them
        # was unavailable. NOT complaints: a complaint means the clause was
        # checked and failed. These say the check did not happen, which a
        # reader must be told rather than left to infer from a PASS.
        self.unverified: list[str] = []

    # -- the live manifests ------------------------------------------------

    def families(self) -> dict[str, str]:
        """`{fact_id: family}` over every nursery manifest.

        The FAMILY is the unit an evaluation record is drawn and scored at, and
        it is a column of the manifests -- so it is read from them, never from
        the amendment. An entry with no `family` simply has none here, and the
        family clause then fails for it rather than matching a `None` against a
        record's `None`.
        """
        if self._families is None:
            families: dict[str, str] = {}
            for path in manifest_paths(self.root):
                document = load_json(path)
                if not isinstance(document, dict):
                    continue
                for entry in document.get("entries") or []:
                    if not isinstance(entry, dict):
                        continue
                    fact_id = entry.get("fact_id")
                    family = entry.get("family")
                    if isinstance(fact_id, str) and isinstance(family, str):
                        families[fact_id] = family
            self._families = families
        return self._families

    def blind(self) -> set[str]:
        """`policy.blind_partitions`, or the empty set when unreadable.

        Read from the policy for ADR-1564's reason: a literal `"held-out"` here
        would be a second copy of a preregistered decision. An unreadable policy
        gives an EMPTY blind set, which makes the direction clause below fail
        for every amendment rather than pass for one -- the safe direction.
        """
        if self._blind is None:
            try:
                self._blind = set(load_policy(self.root).blind)
            except Unanswerable:
                self._blind = set()
        return self._blind

    def resolve(self, endpoint: str) -> str | None:
        """A plain fact id, or the blind row whose salted digest this is.

        An amendment in the `scored-evaluation-residue` class stores its BLIND
        endpoint as the committed baseline's salted digest, because the
        artifact is inside `check-autogenesis-holdout-isolation.py`'s scan set
        and a plain held-out id there is a breach (ADR-1550's first baseline was
        six of them). Resolution is the inverse the gate CAN compute and a
        producer cannot: digest every blind row of the live manifests with the
        committed salt and look the amendment's endpoint up in that map.
        """
        if endpoint in self.partition_of:
            return endpoint
        if self._digests is None:
            salt = committed_salt(self.root)
            blind = self.blind()
            self._digests = ({} if salt is None else
                             {digest_fact_id(fact_id, salt): fact_id
                              for fact_id, partition in self.partition_of.items()
                              if partition in blind})
        return self._digests.get(endpoint)

    def fact_path(self, fact_id: str) -> str | None:
        """The ledger file that DECLARES this fact, relative to the root.

        Globbed from the ledger rather than computed from the id: the pickaxe
        below is only as good as the path it searches, and a guessed
        `F:x` -> `F-x.json` transform that missed would report `no commit adds
        this string` -- a phrase that reads like a finding and would silently
        turn the preregistration clause into a refusal for every amendment.
        """
        if self._paths is None:
            paths: dict[str, str] = {}
            facts_dir = self.root / FACTS_DIR
            if facts_dir.is_dir():
                for path in sorted(facts_dir.glob("*.json")):
                    try:
                        fact = load_json(path)
                    except Unanswerable:
                        continue
                    if isinstance(fact, dict) and isinstance(fact.get("id"), str):
                        paths[fact["id"]] = str(path.relative_to(self.root))
            self._paths = paths
        return self._paths.get(fact_id)

    # -- the evaluation records -------------------------------------------

    def records(self) -> dict[str, dict[str, Any]]:
        """`{record_id: record}` from `EVALUATION_RECORDS_PATH`.

        The file is either ONE record object or a `{"records": [...]}` list;
        both shapes are read, because which one it is has never been decided
        and a gate that reads only today's shape would silently honour nothing
        the day a second record lands.
        """
        if self._records is None:
            records: dict[str, dict[str, Any]] = {}
            path = self.root / EVALUATION_RECORDS_PATH
            if path.is_file():
                try:
                    document = load_json(path)
                except Unanswerable:
                    document = None
                candidates: list[Any] = []
                if isinstance(document, dict):
                    if isinstance(document.get("records"), list):
                        candidates = document["records"]
                    else:
                        candidates = [document]
                for candidate in candidates:
                    if (isinstance(candidate, dict)
                            and isinstance(candidate.get("record_id"), str)):
                        records[candidate["record_id"]] = candidate
            self._records = records
        return self._records

    # -- the commit graph --------------------------------------------------

    def _git(self, *args: str) -> subprocess.CompletedProcess[str] | None:
        try:
            return subprocess.run(["git", *args], cwd=self.root,
                                  capture_output=True, text=True, timeout=60,
                                  check=False)
        except (OSError, subprocess.SubprocessError):
            return None

    def git_available(self) -> bool:
        """Is this root a git work tree at all?

        THE ONE TOLERANCE THIS CLASS HAS, and it is narrow on purpose. Clause
        (b) is a question about the commit graph, and three real trees here do
        not have one: `scripts/tests/mutation_controls.py` copies the checkout
        with `.git` excluded (measured -- it is in `ignore_patterns`), a lane
        snapshot from `git archive | tar -x` has no history either, and the
        control suites build fixture trees from scratch.

        Refusing every amendment in those trees would make this gate red
        wherever it is not the checkout, which is a verdict about where the
        gate ran rather than about the ledger -- the failure mode `exit 2`
        exists to avoid. Honouring them SILENTLY would be worse: the reader
        would be told the clause held when it was never asked.

        So: when there is no work tree, the clause is skipped and RECORDED in
        `unverified`, which both gates print as a `CLASS-UNVERIFIED` line. The
        authoritative run is the one in a checkout, and it says so.
        """
        if self._git_available is None:
            done = self._git("rev-parse", "--is-inside-work-tree")
            self._git_available = (done is not None and done.returncode == 0
                                   and done.stdout.strip() == "true")
        return self._git_available

    def introducing_sha(self, path: str, needle: str) -> str | None:
        """The FIRST commit that put `needle` into `path`, or `None`.

        `--diff-merges=first-parent` for the reason `introducing_commit`
        records: a plain pickaxe skips merges, so an edge that entered during a
        conflict resolution is attributed to nothing at all -- 7 of 198 edges on
        the 2026-09-02 baseline.
        """
        done = self._git("log", "--diff-merges=first-parent", "--no-patch",
                         f"-S{needle}", "--format=%H", "--reverse", "--", path)
        if done is None or done.returncode != 0:
            return None
        lines = done.stdout.strip().splitlines()
        return lines[0].strip() if lines else None

    def strictly_precedes(self, earlier: str, later: str) -> bool:
        """Is `earlier` a git ancestor of `later`, and not the same commit?

        AN ANCESTRY TEST, NOT A TIMESTAMP COMPARISON. A committer date is
        writable and a rebase rewrites it; `merge-base --is-ancestor` answers
        the question the argument actually needs -- was the protocol in the tree
        the edge was written against. STRICT because `is-ancestor` is reflexive:
        a protocol committed in the same commit as the edge it licenses was not
        preregistered, it was co-registered, and that is the shape this clause
        exists to refuse.
        """
        resolved = []
        for revision in (earlier, later):
            done = self._git("rev-parse", "--verify", f"{revision}^{{commit}}")
            if done is None or done.returncode != 0:
                return False
            resolved.append(done.stdout.strip())
        if resolved[0] == resolved[1]:
            return False
        done = self._git("merge-base", "--is-ancestor", resolved[0], resolved[1])
        return done is not None and done.returncode == 0


def class_complaint(item: dict[str, Any], index: int,
                    partition_of: dict[str, str],
                    context: ClassContext | None = None) -> str | None:
    """Why this amendment's declared `class` does not hold, or `None`.

    ADR-1563, extended by ADR-1566. An amendment MAY declare a `class`, and a
    class is a rule the checker re-derives from the LIVE manifests rather than a
    label the author asserts. Two classes exist:

    `depends-on-longitudinal-bootstrap` -- the edge's TARGET sits in the
    `longitudinal` partition. That partition is pinned by
    `check-autogenesis-nursery.py` to exactly the two Autogenesis-1 bootstrap
    lemmas (`F:nat-mul-one`, `F:nat-zero-add`), which are the axioms-of-the-
    library every partition must be free to depend on. An edge INTO one of
    them reveals nothing about the source's partition, because every partition
    has the same access to it and the longitudinal row is never a target of
    evaluation.

    THE DIRECTION IS HALF THE RULE AND IT IS CHECKED. `to_partition ==
    longitudinal` only. The reverse -- a longitudinal fact whose proof depends
    on an evaluation fact -- pulls a drawn result into the regression chain and
    IS a leak; it can never carry this class, so
    `check-autogenesis-nursery.py`'s longitudinal-overlap check stays failable
    in exactly the direction that can fail honestly.

    `scored-evaluation-residue` (ADR-1566) -- the edge is the RESIDUE of an
    evaluation that was scored under a protocol committed before the edge
    existed. A blind row's proof cites the training set; that is what a
    training set is for, and it is what scoring a held-out row looks like. Four
    clauses, each re-derived and each separately deletable:

      (d) the amendment is keyed to `evaluation_record`, the `record_id` of a
          record in `EVALUATION_RECORDS_PATH`. NEVER to a fact id: keying to a
          fact would put a held-out id in an artifact
          `check-autogenesis-holdout-isolation.py` scans, and would turn a
          checkable claim about a committed record into a judgement about a row.
      (a) the edge's blind endpoint belongs to the FAMILY that record names AND
          appears in that record's `outcomes`. Family alone is not enough: a
          sibling nobody evaluated is still an unscored row.
      (b) the record's `state` is `scored`, and its `protocol_commit` is a
          STRICT git ancestor of the commit that introduced this edge. This is
          ADR-1565's whole argument mechanised -- an edge OLDER than the
          protocol was not created by the evaluation, and belongs to the
          ADR-1450 reclassification instrument instead.
      (c) the edge runs FROM the blind row to a non-blind one. An edge INTO a
          blind row spends blindness and is the original breach; it can never
          carry this class, which is what keeps the seal ADR-1565 restored
          failable in the direction that can fail honestly.

    An amendment whose declared class does not hold is REPORTED AND NOT
    HONOURED, the same treatment as a missing field: a class that is a
    self-assigned label rather than a re-derived property is the component
    exemption again with a smaller unit.
    """
    declared = item.get("class")
    if declared is None:
        return None
    if declared not in AMENDMENT_CLASSES:
        return (f"{AMENDMENTS_PATH}[{index}]: class {declared!r} is not one of "
                f"{sorted(AMENDMENT_CLASSES)} -- NOT honoured")
    target_partition = partition_of.get(item["to"])
    if declared == "depends-on-longitudinal-bootstrap":
        if target_partition != "longitudinal":
            return (f"{AMENDMENTS_PATH}[{index}]: claims class "
                    f"depends-on-longitudinal-bootstrap but {item['to']} is in "
                    f"partition {target_partition!r}, not `longitudinal` -- "
                    f"the class is re-derived from the live manifests, not "
                    f"taken on the author's word, so this one is NOT honoured")
    if declared == "scored-evaluation-residue":
        where = f"{AMENDMENTS_PATH}[{index}]"
        if context is None:
            return (f"{where}: claims class scored-evaluation-residue but no "
                    f"class context was built, so none of its four clauses "
                    f"could be re-derived -- NOT honoured")
        # (d) KEYED TO THE EVALUATION RECORD, NEVER TO A FACT.
        #
        # `records.get(record_id, {})` rather than `records[record_id]` on
        # purpose: with this clause deleted (the mutant), an unkeyed amendment
        # must fall through to the NEXT clause and be refused there, not crash
        # the gate on a KeyError. A guard whose mutant produces a traceback
        # cannot be told apart from a guard whose mutant produces a wrong
        # verdict, and only the second is what mutation is measuring.
        record_id = item.get("evaluation_record")
        records = context.records()
        if not isinstance(record_id, str) or record_id not in records:
            return (f"{where}: class scored-evaluation-residue must name "
                    f"`evaluation_record`, the record_id of a record in "
                    f"{EVALUATION_RECORDS_PATH}; {record_id!r} is not one of "
                    f"{sorted(records)} -- the class is keyed to the "
                    f"evaluation, never to a fact, so this one is NOT honoured")
        record = records.get(record_id, {}) if isinstance(record_id, str) else {}
        source = context.resolve(item["from"])
        target = context.resolve(item["to"])
        if source is None or target is None:
            return (f"{where}: claims class scored-evaluation-residue but an "
                    f"endpoint resolves to no row of the live manifests (it is "
                    f"neither a drawn fact id nor the committed salted digest "
                    f"of one) -- NOT honoured")
        blind = context.blind()
        # (c) THE DIRECTION IS HALF THE RULE.
        if partition_of.get(source) not in blind or partition_of.get(target) in blind:
            return (f"{where}: claims class scored-evaluation-residue but the "
                    f"edge does not run FROM a blind row "
                    f"({partition_of.get(source)!r}) TO a non-blind one "
                    f"({partition_of.get(target)!r}); an edge INTO a blind row "
                    f"spends blindness and is the breach this class is not "
                    f"about -- NOT honoured")
        # (a) THE FAMILY IS SCORED, AND THIS ROW IS ONE OF THE SCORED ONES.
        #
        # The clause is about the BLIND ENDPOINT, whichever end that is -- not
        # about `source`. Written against `source` it would ALSO fire on a
        # reversed (into-the-blind-row) edge, and clause (c) could then never
        # be the only thing refusing one: its mutant would kill nothing, which
        # is a guard that reads as present and measures nothing.
        blind_endpoint = (source if partition_of.get(source) in blind
                          else target)
        scored_ids = {outcome.get("fact_id")
                      for outcome in record.get("outcomes") or []
                      if isinstance(outcome, dict)}
        if (context.families().get(blind_endpoint) != record.get("family")
                or blind_endpoint not in scored_ids):
            return (f"{where}: claims class scored-evaluation-residue against "
                    f"record {record_id!r}, but its blind endpoint is not a "
                    f"scored row of family {record.get('family')!r} in that "
                    f"record's outcomes -- a sibling of a spent family is "
                    f"still a row nobody evaluated, so this one is NOT "
                    f"honoured")
        # (b) THE PREREGISTRATION PREDATES THE EDGE.
        #
        # The pickaxe searches for the RESOLVED target id, never `item["to"]`:
        # an endpoint may be written here as a salted digest, and a digest
        # appears in no fact file, so searching the written form would report
        # `no commit adds this string` for every redacted amendment and turn
        # this clause into a blanket refusal that looks like a finding.
        # TWO guards, not one conjunction, because they refuse different
        # things and a mutant that deletes both at once would kill two tests
        # and say which of the two properties is load-bearing for neither.
        if record.get("state") != "scored":
            return (f"{where}: claims class scored-evaluation-residue against "
                    f"record {record_id!r}, but that record's state is "
                    f"{record.get('state')!r}, not `scored` -- a "
                    f"preregistration is not a result, so this one is NOT "
                    f"honoured")
        protocol_commit = record.get("protocol_commit")
        path = context.fact_path(source)
        edge_commit = (None if path is None
                       else context.introducing_sha(path, target))
        if not context.git_available():
            context.unverified.append(
                f"{where}: the preregistration clause of "
                f"scored-evaluation-residue was NOT re-derived -- "
                f"{context.root} is not a git work tree, so whether "
                f"{record_id!r}'s protocol_commit precedes the commit that "
                f"introduced this edge could not be asked. The amendment is "
                f"honoured here; the authoritative run is the one in a "
                f"checkout")
        elif (not isinstance(protocol_commit, str)
                or edge_commit is None
                or not context.strictly_precedes(protocol_commit, edge_commit)):
            return (f"{where}: claims class scored-evaluation-residue against "
                    f"record {record_id!r}, but its protocol_commit is not a "
                    f"strict git ancestor of the commit introducing this edge "
                    f"(protocol_commit={protocol_commit!r}, "
                    f"introduced_by={edge_commit!r}) -- an edge older than the "
                    f"protocol was not created by the evaluation, so this one "
                    f"is NOT honoured")
    return None


def load_amendments(
    root: pathlib.Path, partition_of: dict[str, str],
    unverified: list[str] | None = None,
) -> tuple[set[tuple[str, str]], list[str]]:
    """The per-edge amendments, and the complaints about anything that is not one.

    An amendment names ONE edge (`from`, `to`), a `reason` and a `date`. An
    element missing any of those is REPORTED AND NOT HONOURED rather than
    quietly skipped: a malformed amendment is a committed defect, and reading
    it as absent is how an exemption list stops being reviewable.

    An optional `class` is validated against the live manifests by
    `class_complaint` and, when it does not hold, kills the amendment the same
    way a missing field does.
    """
    path = root / AMENDMENTS_PATH
    if not path.is_file():
        return set(), []
    document = load_json(path)
    complaints: list[str] = []
    amendments: set[tuple[str, str]] = set()
    context = ClassContext(root, partition_of)
    raw = document.get("amendments") if isinstance(document, dict) else None
    if not isinstance(raw, list):
        return set(), [f"{AMENDMENTS_PATH}: `amendments` is not a list; "
                       f"nothing in it is honoured"]
    for index, item in enumerate(raw):
        if not isinstance(item, dict):
            complaints.append(f"{AMENDMENTS_PATH}[{index}]: not an object")
            continue
        missing = [k for k in ("from", "to", "reason", "date")
                   if not isinstance(item.get(k), str) or not item[k]]
        if missing:
            complaints.append(
                f"{AMENDMENTS_PATH}[{index}]: missing {', '.join(missing)} -- "
                f"an amendment names ONE edge, its reason and its date, so "
                f"this one is NOT honoured")
            continue
        wrong_class = class_complaint(item, index, partition_of, context)
        if wrong_class:
            complaints.append(wrong_class)
            continue
        amendments.add((item["from"], item["to"]))
    if unverified is not None:
        unverified.extend(context.unverified)
    return amendments, complaints


def count_style_exemptions(
    root: pathlib.Path,
) -> tuple[list[str], set[tuple[str, str]]]:
    """Report every component/count-shaped exemption, and the edges it COVERS.

    Returns `(report lines, the ordered pairs a component exemption would
    suppress if this gate honoured it)`. THE SECOND VALUE IS REPORTED AND
    NEVER SUBTRACTED -- see `main`, where the honoured set is the per-edge
    amendments and nothing else, on one line so that honouring these is a
    mutation somebody can write and `mutation_controls.py` can register.

    Computing the pairs rather than hardcoding an empty set is what makes the
    refusal measurable: the report can say how many live violations a
    component exemption WOULD have waved through, which is the number
    ADR-1546 could not state about the gate it audited.
    """
    lines: list[str] = []
    covered: set[tuple[str, str]] = set()
    for path in manifest_paths(root):
        document = load_json(path)
        if not isinstance(document, dict):
            continue
        rel = str(path.relative_to(root))
        for key in COUNT_STYLE_EXEMPTION_KEYS:
            value = document.get(key)
            if not isinstance(value, list) or not value:
                continue
            for index, item in enumerate(value):
                members = (item.get("component_fact_ids")
                           if isinstance(item, dict) else None)
                size = len(members) if isinstance(members, list) else "?"
                lines.append(
                    f"NOT-AN-AMENDMENT {rel}:{key}[{index}] names a component "
                    f"of {size} fact ids and no edge; unparseable as a "
                    f"per-edge amendment, so it suppresses nothing here")
                if not isinstance(members, list):
                    continue
                inside = [m for m in members if isinstance(m, str)]
                for source in inside:
                    for target in inside:
                        if source != target:
                            covered.add((source, target))
    return lines, covered


# --------------------------------------------------------------------------
# Attribution
# --------------------------------------------------------------------------

def introducing_commit(root: pathlib.Path, edge: dict[str, str]) -> str:
    """The commit that first put this dependency string into this fact file.

    A pickaxe search over the SOURCE fact's own file, oldest first. Tolerant
    by construction: the ownership sandbox and the control suites' throwaway
    trees are not this repository, and a gate that died because it could not
    run a version-control query would be answering a question nobody asked.

    `--diff-merges=first-parent` IS LOAD-BEARING AND WAS MEASURED. A plain
    pickaxe skips merge commits entirely, so an edge that entered the tree
    during a conflict resolution -- an evil merge -- is attributed to NOTHING.
    On the 2026-09-02 baseline that is **7 of 198** crossing edges, every one
    of them reported as `no commit adds this string` while the string is
    plainly in the committed file. The first of the seven,
    `F:ml430-int-add-comm-c5722728 -> F:ml430-nat-add-comm-56a2d614`, was
    introduced by the merge `0be9ff41b` and by no other commit in the file's
    nine-commit history (verified by walking every one of them and counting
    occurrences, not by trusting the pickaxe that had just said nothing).
    `--no-patch` is what keeps the merge diff itself out of the output.
    """
    path = edge.get("declared_in")
    if not path:
        return "unknown (no fact file)"
    try:
        done = subprocess.run(
            ["git", "log", "--diff-merges=first-parent", "--no-patch",
             f"-S{edge['to']}", "--format=%h %ad",
             "--date=short", "--reverse", "--", path],
            cwd=root, capture_output=True, text=True, timeout=60, check=False)
    except (OSError, subprocess.SubprocessError):
        return "unknown (version control unavailable)"
    if done.returncode != 0:
        return "unknown (version control query failed)"
    first = done.stdout.strip().splitlines()
    return first[0] if first else "unknown (no commit adds this string)"


# --------------------------------------------------------------------------
# The baseline
# --------------------------------------------------------------------------

def read_baseline(root: pathlib.Path) -> dict[str, Any]:
    path = root / BASELINE_PATH
    if not path.is_file():
        raise Unanswerable(
            f"{BASELINE_PATH} is absent -- --baseline cannot ratchet against a "
            f"baseline that does not exist. Record one with "
            f"--record-baseline, or run without --baseline for the full set.")
    document = load_json(path)
    if not isinstance(document, dict) or not isinstance(document.get("edges"), list):
        raise Unanswerable(f"{BASELINE_PATH}: no `edges` list")
    return document


def baseline_keys(document: dict[str, Any]) -> set[tuple[str, str]]:
    return {(e.get("from"), e.get("to")) for e in document["edges"]
            if isinstance(e, dict)}


def head_commit(root: pathlib.Path) -> str:
    try:
        done = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                              capture_output=True, text=True, timeout=30,
                              check=False)
    except (OSError, subprocess.SubprocessError):
        return "unknown"
    return done.stdout.strip() or "unknown"


def ledger_digest(partition_of: dict[str, str],
                  dependencies: dict[str, tuple[list[str], str]]) -> str:
    """A digest of the drawn population's declared dependencies.

    Recorded as PROVENANCE (`this edge set was measured against this ledger
    state`), never recomputed into the committed file on a later run -- see
    `render_baseline`.
    """
    return sha256_of([[fact_id, partition_of[fact_id],
                       sorted(dependencies.get(fact_id, ([], ""))[0])]
                      for fact_id in sorted(partition_of)])


def render_baseline(root: pathlib.Path, edges: list[dict[str, str]],
                    manifests: list[str], ledger_sha: str,
                    previous: dict[str, Any] | None, salt: str) -> str:
    """The committed baseline text.

    `recorded_date`, `recorded_at_commit` and `ledger_sha256` are PROVENANCE
    and are carried forward unchanged whenever the edge set is unchanged. That
    is not cosmetic: `check-generated-artifact-ownership.py`'s OWNER arm
    requires the owner to restore a perturbed copy BYTE-FOR-BYTE, and a field
    stamped with `today` or with a live digest of a ledger that other lanes
    edit hourly would make this artifact impossible to own. A date that moves
    only when the recorded finding moves is also the more honest field.

    `salt` (and therefore every digested endpoint) is provenance of the same
    kind, and `carry_over` is computed in the REDACTED representation --
    `redacted_key(e, salt)`, not bare `edge_key(e)` -- because `salt` is
    already `resolve_salt(previous)`'s choice: reused when unchanged, so an
    edge set that has not moved must compare equal to what the previous file
    already recorded in ITS (also redacted) representation, or the file would
    be rewritten -- and every held-out digest with it -- on every no-op run.
    """
    rows = [redacted_row(e, salt) for e in edges]
    carry_over = (previous is not None
                  and baseline_keys(previous) == {redacted_key(e, salt)
                                                   for e in edges})
    if carry_over:
        recorded_date = previous.get("recorded_date", "unknown")
        recorded_at_commit = previous.get("recorded_at_commit", "unknown")
        ledger_sha256 = previous.get("ledger_sha256", ledger_sha)
    else:
        recorded_date = datetime.date.today().isoformat()
        recorded_at_commit = head_commit(root)
        ledger_sha256 = ledger_sha
    document = {
        "kind": "axeyum-partition-edge-baseline",
        "authority": "docs/research/09-decisions/adr-1550-gate-the-producer-"
                     "the-crossing-edge-is-the-unit.md",
        "produced_by": "scripts/check-partition-edges.py --record-baseline",
        "rule": "This set may only SHRINK. --record-baseline refuses a set "
                "that is not a subset of the committed one, so a new crossing "
                "cannot be silenced by re-recording; it must be repaired or "
                "carry a per-edge amendment. A held-out endpoint is stored as "
                "a salted SHA-256 digest (`held_out_endpoint: true`), never as "
                "the fact id -- see `redacted_key` in the script.",
        "manifests": manifests,
        "recorded_date": recorded_date,
        "recorded_at_commit": recorded_at_commit,
        "ledger_sha256": ledger_sha256,
        "held_out_salt": salt,
        "edge_set_sha256": sha256_of(rows),
        "edge_count": len(rows),
        "edges": rows,
        "schema_version": 1,
    }
    return json.dumps(document, indent=2, sort_keys=True,
                      ensure_ascii=False) + "\n"


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=None,
                        help="check this tree instead of the checkout")
    parser.add_argument("--baseline", action="store_true",
                        help="fail only on edges absent from the recorded "
                             "baseline (the ratchet; this is the gate form)")
    parser.add_argument("--record-baseline", action="store_true",
                        help="write the current crossing edge set to "
                             + BASELINE_PATH)
    parser.add_argument("--no-blame", action="store_true",
                        help="skip the per-edge commit attribution")
    parser.add_argument("--json", action="store_true",
                        help="emit the violation set as JSON")
    parser.add_argument("--verbose", action="store_true",
                        help="list every declined component exemption even "
                             "when the run passes")
    args = parser.parse_args(argv)

    root = pathlib.Path(args.root
                        or os.environ.get("AXEYUM_PARTITION_EDGES_ROOT")
                        or DEFAULT_ROOT).resolve()

    try:
        partition_of, manifests = load_partitions(root)
        roles = load_policy(root)
        dependencies = load_dependencies(root)
        edges = crossing_edges(partition_of, dependencies, roles)
        class_unverified: list[str] = []
        amendments, amendment_complaints = load_amendments(root, partition_of,
                                                           class_unverified)
        # The salt an amendment's BLIND endpoint is written with. Read from the
        # committed baseline on EVERY path, not only under `--baseline`: an
        # amendment is honoured (or not) identically whether the run is
        # ratcheting, recording, or reporting the full set, and a salt that
        # existed on one path only would make `--record-baseline` re-record the
        # very edges an amendment covers.
        amendment_salt = committed_salt(root)
        not_amendments, component_covered = count_style_exemptions(root)
        previous: dict[str, Any] | None = None
        if (root / BASELINE_PATH).is_file():
            candidate = load_json(root / BASELINE_PATH)
            if isinstance(candidate, dict) and isinstance(candidate.get("edges"), list):
                previous = candidate
        baseline: set[tuple[str, str]] = set()
        baseline_salt: str | None = None
        if args.baseline:
            baseline_document = read_baseline(root)
            baseline = baseline_keys(baseline_document)
            candidate_salt = baseline_document.get("held_out_salt")
            if isinstance(candidate_salt, str) and candidate_salt:
                baseline_salt = candidate_salt
    except Unanswerable as exc:
        print(f"PARTITION-EDGES|UNANSWERABLE {exc}")
        return 2

    if args.record_baseline:
        # THE RECORDED SET EXCLUDES EVERY HONOURED AMENDMENT (ADR-1563). An
        # amended edge is one somebody DECIDED to keep and wrote a per-edge,
        # class-checked reason for; a baselined edge is one nobody has repaired
        # yet. Keeping an edge in both would mean deleting its amendment
        # changes nothing -- the amendment would be un-deletable decoration and
        # `class_complaint` would gate nothing observable. Excluding it makes
        # the amendment load-bearing: drop it and the edge is a violation
        # against a baseline it is no longer in.
        #
        # A malformed or wrongly-classed amendment is printed HERE too, because
        # it is not honoured and its edge therefore stays in the recorded set;
        # a lane that recorded a baseline without seeing why an amendment was
        # refused would read the unshrunk count as the amendment not mattering.
        for line in amendment_complaints:
            print(f"AMENDMENT-REJECTED {line}")
        for line in class_unverified:
            print(f"CLASS-UNVERIFIED {line}")
        return record(root, [e for e in edges
                             if not edge_is_amended(e, amendments, amendment_salt)],
                      manifests, partition_of, dependencies, previous)

    # THE HONOURED SET IS THE PER-EDGE AMENDMENTS AND NOTHING ELSE. This one
    # line is ADR-1550: `component_covered` holds every pair a manifest's
    # component exemption would suppress, it is REPORTED below, and it is not
    # unioned in here. `mutation_controls.py` registers the mutant that unions
    # it, because a refusal nobody can delete is not a decision.
    honoured = amendments
    amended = [e for e in edges if edge_is_amended(e, honoured, amendment_salt)]
    # `redacted_key(e, baseline_salt)`, not `edge_key(e)`: a live held-out
    # crossing must be compared against the DIGESTED form the committed
    # baseline actually stores, or it can never be recognised as already
    # baselined -- see `redacted_key`'s docstring. `edge_is_amended` is the
    # same rule one artifact over (ADR-1566).
    baselined = [e for e in edges
                 if not edge_is_amended(e, honoured, amendment_salt)
                 and redacted_key(e, baseline_salt) in baseline]
    violations = [e for e in edges
                  if not edge_is_amended(e, honoured, amendment_salt)
                  and redacted_key(e, baseline_salt) not in baseline]
    would_be_waved = len([e for e in violations
                          if edge_key(e) in component_covered])

    # The declined component exemptions are listed in full whenever the run
    # has something to say, and summarised as `not_amendments=N` otherwise --
    # this runs on every push and seven standing lines of "still not honoured"
    # is how a gate teaches people to stop reading it. The COUNT is always in
    # the summary, so a new exemption appearing is still visible.
    if violations or args.verbose:
        for line in not_amendments:
            print(line)
    for line in amendment_complaints:
        print(f"AMENDMENT-REJECTED {line}")
    for line in class_unverified:
        print(f"CLASS-UNVERIFIED {line}")

    if args.baseline:
        repaired = sorted(baseline - {redacted_key(e, baseline_salt)
                                      for e in edges})
        for source, target in repaired:
            print(f"REPAIRED {source} -> {target} no longer crosses; "
                  f"re-record the baseline to lock the gain in")

    if args.json:
        print(json.dumps({"violations": violations, "amended": amended,
                          "baselined": baselined}, indent=2, sort_keys=True))

    for edge in violations:
        blame = ("blame-skipped" if args.no_blame
                 else introducing_commit(root, edge))
        print(f"FAIL: {edge['from']} [{edge['from_partition']}] "
              f"depends_on {edge['to']} [{edge['to_partition']}] "
              f"-- introduced by {blame}")

    unamended_total = len([e for e in edges
                           if not edge_is_amended(e, honoured, amendment_salt)])
    summary = (f"PARTITION-EDGES|manifests={len(manifests)}"
               f"|{roles.summary()}"
               f"|drawn={len(partition_of)}"
               f"|crossing={len(edges)}"
               f"|amended={len(amended)}"
               f"|baselined={len(baselined)}"
               f"|violations={len(violations)}"
               f"|not_amendments={len(not_amendments)}"
               f"|component_exemptions_would_wave={would_be_waved}"
               f"|class_unverified={len(class_unverified)}")
    if violations:
        print(summary + "|FAILED")
        print(f"  {len(violations)} `depends_on` edge(s) cross an evaluation "
              f"partition and are covered by no per-edge amendment.")
        print("  A crossing edge fuses two evaluation partitions: a held-out "
              "result stops being blind and a train/development split stops "
              "meaning anything. Repair the edge (drop the dependency, or "
              "route through a fact in the same partition), or record a "
              "per-edge amendment in " + AMENDMENTS_PATH + " naming the edge, "
              "a reason and a date. Enlarging a component exemption does "
              "NOTHING here -- see ADR-1550.")
        return 1
    print(summary + f"|unamended_total={unamended_total}|PASS")
    return 0


def record(root: pathlib.Path, edges: list[dict[str, str]],
           manifests: list[str], partition_of: dict[str, str],
           dependencies: dict[str, tuple[list[str], str]],
           previous: dict[str, Any] | None) -> int:
    """Write the baseline, refusing any set that is not a subset of the old one.

    THE RATCHET IS HERE, not in the reading. `--baseline` is only as strong as
    the file it reads, so if re-recording could enlarge the set, a lane that
    hit the gate could clear it in one command and the whole scheme would be
    the growing component exemption again under a new name.

    `keys` is computed with `redacted_key`, using `resolve_salt(previous)` --
    the SAME salt the committed file already uses when one exists -- so a
    held-out crossing that is already in `previous` compares equal here too.
    Using bare `edge_key` would compare a fresh plain id against a committed
    digest and see every held-out crossing as new on every run, which would
    make the ratchet un-recordable the moment it holds one.
    """
    salt = resolve_salt(previous)
    keys = {redacted_key(e, salt) for e in edges}
    if previous is not None:
        grew = sorted(keys - baseline_keys(previous))
        if grew:
            print("PARTITION-EDGES|REFUSED-TO-GROW-BASELINE")
            for source, target in grew:
                print(f"  NEW {source} -> {target}")
            print(f"  {len(grew)} edge(s) are not in the committed baseline. "
                  f"The baseline may only SHRINK (ADR-1550): a new crossing "
                  f"is repaired or amended per edge, never absorbed. Nothing "
                  f"was written.")
            return 1
    text = render_baseline(root, edges, manifests,
                           ledger_digest(partition_of, dependencies), previous,
                           salt)
    (root / BASELINE_PATH).write_text(text)
    shrank = 0 if previous is None else len(baseline_keys(previous) - keys)
    print(f"PARTITION-EDGES|RECORDED|edges={len(edges)}|shrank_by={shrank}"
          f"|{BASELINE_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
