#!/usr/bin/env python3
"""Derive the obstruction graph from typed declines. Never hand-authored.

Autogenesis F3 (`docs/autogenesis/243-knowledge-overlay-and-fill-plan.md`) asks
for one thing this repository did not have: an obstruction record that separates
the FIRST observed blocker from the COMPLETE known blocker set, names the
affected population and its partition, counts the facts blocked, names a
candidate capability and says whether it already exists, and carries a
before/after funnel with a resolution commit. Doc 243's own rule is that such a
graph must be *derived*: "do not add a generator until at least two manually
reviewed batches expose the real repetition" -- and the batches now exist, so
the graph is generated and a hand-edited row is a defect.

Two evidence populations, deliberately kept distinguishable:

* the **16 committed agent episodes** under `artifacts/episodes/<date>[-<slice>]/`
  (slice A2 and A4 of `docs/python-2026-08/03-agentic-layer.md`), whose declines
  are typed values -- a `NoGeneralRoute` proposal variant, a v2 `decline_class`
  enum -- rather than prose;
* the **11 committed producer decline records** `artifacts/autogenesis/*-decline-v*.json`,
  which predate the loop and carry no episode fields at all.

`artifacts/episodes/fixtures*/` is NOT read. Those documents are the
`check-agent-episode.py` control suite's own inputs -- hand-authored, some of
them deliberately corrupt -- and counting them would put invented declines in a
census whose whole value is that it is measured. Only directories named for a
date contribute, which is the committed naming convention and does not need a
new list every time a slice lands.

WHAT THIS FILE REFUSES TO DO, and why each refusal is a guard rather than taste:

1.  **Exit 1 when no obstruction was derived.** A census that found nothing and
    exited 0 is the checker-that-cannot-fail defect: it would report a clean
    frontier for a directory that does not exist.
2.  **Exit 1 when any decline record's shape matches no predicate.** A new
    decline shape that silently vanished from the census is the same defect one
    arrow upstream -- the graph would keep exiting 0 while measuring less and
    less of the world.
3.  **Exit 1 when any population, or any byte of the rendered document, names a
    held-out fact id.** Both directions are checked: the structured populations
    AND a generic string walk, because operations already carried fact ids at
    three distinct JSON paths and a field-specific guard was bypassable the day
    it was written (`scripts/check-autogenesis-holdout-isolation.py`).
4.  **Drop must-decline mutations from a population.** A producer declining a
    FALSE statement is the trusted layer working, not an obstruction, and
    counting the nine preregistered `must-decline-mutations-v1.json` rows as
    blocked facts would inflate every cluster that happens to contain one.

Deterministic: sorted keys throughout, cluster ids are sha256 of the cluster key
so nothing is assigned by judgement, and `--check` exits 1 when the committed
artifact differs from a regeneration.

Stdlib only. Nothing under `scripts/` may import the `[agent]` extra; the
Python-side twin of the classification lives in `python/axeyum/agent/classify.py`
and `python/tests/test_agent_classify.py` asserts the two agree on every
committed episode.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
EPISODES = ROOT / "artifacts/episodes"
AUTOGENESIS = ROOT / "artifacts/autogenesis"
NURSERY = AUTOGENESIS / "nursery-v1.json"
OVERLAY = AUTOGENESIS / "knowledge-overlay-v1.json"
CATALOG = AUTOGENESIS / "tactic-catalog-v1.json"
MUST_DECLINE = AUTOGENESIS / "must-decline-mutations-v1.json"
FACTS = ROOT / "artifacts/facts"
OUTPUT = AUTOGENESIS / "obstruction-graph-v1.json"

#: An episode directory is named for the day it was run, optionally with the
#: slice that ran it: `2026-08-24`, `2026-08-24-a4`. `fixtures` and
#: `fixtures-v2` do not match, which is the point.
EPISODE_DIR = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}(?:-[a-z0-9]+)?$")
FACT_ID = re.compile(r"^F:[a-z0-9]+(?:-[a-z0-9]+)*$")
DECLINE_RECORD = re.compile(r"-decline-v[0-9]+\.json$")

#: A tier-C tool call is the only thing that can carry `checked` assurance
#: (`axeyum.agent.tools.TOOL_TIERS` is its single source), so this is how an
#: episode says a producer was actually dispatched.
CHECKED = "checked"

#: The independent kernel re-check, and the registry/transaction proposal. They
#: are matched on the committed command strings rather than on position: an
#: episode records both in `checker_runs[]` and their order is not a contract.
RECONSTRUCTION_COMMAND = "python -m axeyum.agent check"
CHECKER_COMMAND = "prepare-autogenesis-fact-transaction.py"


class DeriveError(Exception):
    """Fail closed. Every raise here is a refusal to commit a census."""


# --------------------------------------------------------------- small helpers


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return sha256_bytes(path.read_bytes())


def cluster_id(cluster_key: str) -> str:
    """`O:<kind>-<8 hex>`, where the hex is sha256 of the whole cluster key.

    The kind is in the id so a reader can see what a cluster is without a
    lookup; the digest is what makes it stable and unassignable. Both halves
    are re-derivable by hand from `cluster_key`, which is why that field is
    printed in the artifact.
    """
    kind = cluster_key.split("|", 1)[0]
    return f"O:{kind}-{sha256_bytes(cluster_key.encode('utf-8'))[:8]}"


def link_id(relation: str, source: str, target: str) -> str:
    digest = sha256_bytes(f"{relation}|{source}|{target}".encode("utf-8"))[:12]
    return f"L:obs-{digest}"


def repo_relative(path: pathlib.Path) -> str:
    return str(path.relative_to(ROOT))


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise DeriveError(f"{path}: cannot read JSON: {error}") from error


def walk_strings(node: Any):
    if isinstance(node, dict):
        for value in node.values():
            yield from walk_strings(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk_strings(value)
    elif isinstance(node, str):
        yield node


def keyed_fact_ids(node: Any, key: str | None = None):
    """Fact ids under a key named `*fact_id` or an item of a `*fact_ids` list.

    A generic string walk would also pick up ids quoted inside prose -- the
    descfactorial record names `F:nat-zero-add` inside a sentence about what
    would close the cluster, which is a suggestion and not a member of the
    blocked population. Keying the walk is what keeps the population to what a
    record DECLARED.
    """
    if isinstance(node, dict):
        for child_key, value in node.items():
            yield from keyed_fact_ids(value, child_key)
    elif isinstance(node, list):
        for value in node:
            if isinstance(value, str) and key is not None and key.endswith("fact_ids"):
                if FACT_ID.match(value):
                    yield value
            else:
                yield from keyed_fact_ids(value, key)
    elif isinstance(node, str):
        if key is not None and key.endswith("fact_id") and FACT_ID.match(node):
            yield node


# ------------------------------------------------------------- reference data


def held_out_ids() -> set[str]:
    """The blind population, read from the nursery. Fail closed when empty.

    An empty held-out set would make every held-out assertion in this file pass
    vacuously, which is the "guard whose subject has vanished" failure the
    isolation gate documents.
    """
    manifest = load_json(NURSERY)
    entries = manifest.get("entries")
    if not isinstance(entries, list) or not entries:
        raise DeriveError(f"{NURSERY}: no entries; refusing to derive a census against it")
    held = {
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict) and entry.get("partition") == "held-out"
    }
    if not held:
        raise DeriveError(f"{NURSERY}: held-out population is empty; refusing a vacuous guard")
    return held


def partitions_and_families() -> tuple[dict[str, str], dict[str, str]]:
    manifest = load_json(NURSERY)
    partition = {}
    family = {}
    for entry in manifest["entries"]:
        if isinstance(entry, dict) and isinstance(entry.get("fact_id"), str):
            partition[entry["fact_id"]] = entry.get("partition", "unregistered")
            family[entry["fact_id"]] = entry.get("family", "unregistered")
    return partition, family


def must_decline_ids() -> set[str]:
    """Preregistered FALSE statements. Declining one is correct, not blocked."""
    document = load_json(MUST_DECLINE)
    return {
        row["fact_id"]
        for row in document.get("entries", [])
        if isinstance(row, dict) and isinstance(row.get("fact_id"), str)
    }


def overlay_capabilities() -> set[str]:
    document = load_json(OVERLAY)
    return {
        entity["id"]
        for entity in document.get("entities", [])
        if isinstance(entity, dict) and entity.get("kind") == "capability"
    }


def tactic_capabilities() -> dict[str, str]:
    document = load_json(CATALOG)
    return {
        row["id"]: row["realizes"]
        for row in document.get("tactics", [])
        if isinstance(row, dict) and "id" in row and "realizes" in row
    }


# ------------------------------------------------------- capability candidates
#
# One entry per blocker kind. Every `reason` is quoted or paraphrased from the
# evidence that produced the kind -- the decline records name what would close
# their cluster in `next_boundary` / `next` / `what_would_close_the_cluster`,
# and the episode findings are recorded in plan 03's A4 result block. Nothing
# here is a guess about a capability nobody wrote down.
CANDIDATES: dict[str, tuple[str, str]] = {
    "no-general-route": (
        "K:proposed-tactic-precondition-mobility-census",
        "The model declined to claim a route generalizes, having seen the whole eligible "
        "page. Plan 03's A4 finding 3 measured that this rule filters the model's "
        "CONFIDENCE that a route generalizes, not whether it does -- 1 of 3 exportable "
        "ModEq facts was a false negative. Running every tactic precondition against every "
        "open fact with no model in the loop (slice A7) supplies the sibling evidence "
        "mechanically, which is what the three-sibling rule is asking for.",
    ),
    "gate-refused": (
        "K:proposed-tactic-precondition-mobility-census",
        "The deterministic gate refuses a NoGeneralRoute plan by design. The gate is not "
        "the obstruction; the absence of mechanical sibling evidence upstream of it is.",
    ),
    "export-missing": (
        "K:bounded-reproducible-export",
        "The producer had no frozen, proof-free statement export to import. Plan 03's A4 "
        "finding 2 measured that exactly 3 of 98 eligible facts have one, so this is the "
        "bottleneck between the loop and volume; the overlay already carries this candidate "
        "capability on the evidence of retained exporter/module/root decline records.",
    ),
    "budget": (
        "K:proposed-retrieval-budget-policy",
        "The run spent its request and tool-call limits on tier-R gathering and never "
        "reached, or never finished, a plan. Budget exhaustion is a verdict rather than an "
        "error here, so the measurable fix is an allocation policy between retrieval and "
        "planning, not a larger ceiling.",
    ),
    "axiom-footprint-nonempty": (
        "K:proposed-axiom-free-recursion-scheme",
        "The kernel accepted the declaration and the measured axiom footprint was not "
        "empty. Every record in this cluster asks for the same thing in its own words: a "
        "route whose induction principle is explicit in the authored term, so the target "
        "does not depend on Lean's generated well-founded-recursion theorem.",
    ),
    "elaboration-blocked": (
        "K:proposed-explicit-term-construction",
        "The Lean elaborator refused the authored term -- it would not unfold an opaque "
        "public definition, or left a combinator metavariable-polymorphic. Both records "
        "ask for the same remedy: construct the term explicitly from proof-free statements "
        "rather than relying on the elaborator to resolve it.",
    ),
    "tooling-gate-refused": (
        "K:proposed-producer-driver-scaffold",
        "This repository's own lint gate refused the producer driver before it read a "
        "single stream. Both records' next step is to extract the same helper, so the "
        "obstruction is the absence of a shared driver scaffold rather than either defect.",
    ),
    "tactic-precondition-unmatched": (
        "K:bounded-structural-induction",
        "The record states what would close the cluster: a producer that can discharge one "
        "step of Nat.zero_add / Nat.add_zero / Nat.mul_one beyond bare Eq.refl, using facts "
        "this ledger's own Nat prelude has already proved. That is bounded induction with "
        "IH-congruence rewriting, which is an ACTIVE capability in the overlay -- the "
        "finding is that it has not been pointed at this population, not that it is missing.",
    ),
    "replay-readiness-mismatch": (
        "K:proposed-hermetic-replay-checkout",
        "The replay driver verified retained readiness against a checkout whose gate "
        "surface had moved. Both records' next step is to run the unchanged driver from a "
        "clean detached checkout of the exact transition commit.",
    ),
}


# ------------------------------------------------------------------- episodes


def episode_paths() -> list[pathlib.Path]:
    paths: list[pathlib.Path] = []
    if not EPISODES.is_dir():
        raise DeriveError(f"{EPISODES}: episode tree is missing")
    for directory in sorted(EPISODES.iterdir()):
        if directory.is_dir() and EPISODE_DIR.match(directory.name):
            paths.extend(sorted(directory.glob("episode-*.json")))
    if not paths:
        raise DeriveError(f"{EPISODES}: no dated episode directories; nothing to derive from")
    return paths


def episode_funnel(document: dict) -> dict[str, int]:
    """The six F3 stages as predicates over one episode document.

    Every one of them reads a field the episode already has. Slice A5 adds no
    field to the v2 schema, which is deliberate: a taxonomy that needed a new
    column would be a taxonomy the committed episodes could not be scored
    against.
    """
    outcome = document["outcome"]
    calls = document["transcript"]["tool_calls"]
    runs = outcome.get("checker_runs", [])
    dispatched = any(call.get("assurance") == CHECKED for call in calls)
    adapter = dispatched and outcome.get("decline_class") != "retrieval-miss"
    producer = adapter and (outcome["verdict"] == "proved" or bool(runs))
    reconstruction = any(
        run.get("exit_status") == 0 and str(run.get("command", "")).startswith(RECONSTRUCTION_COMMAND)
        for run in runs
    )
    checker = any(
        run.get("exit_status") == 0 and CHECKER_COMMAND in str(run.get("command", ""))
        for run in runs
    )
    return {
        "goal": 1,
        "adapter": int(adapter),
        "producer": int(producer),
        "reconstruction": int(reconstruction),
        "checker": int(checker),
        "obstruction": int(outcome["verdict"] != "proved"),
    }


def episode_proposals(path: pathlib.Path, document: dict) -> list[dict]:
    rows = []
    for row in document.get("proposals", []):
        proposal_path = ROOT / row["path"]
        if not proposal_path.is_file():
            raise DeriveError(f"{path}: proposal {row['path']} is missing from disk")
        rows.append(load_json(proposal_path))
    return rows


def classify_episode(document: dict, proposals: list[dict]) -> tuple[dict, list[dict], str]:
    """`(first blocker, known blockers, coarse cluster detail)` for one episode.

    The FIRST blocker is what the run hit first in time, which is not the same
    as the class the episode recorded. An A4 episode whose model emitted
    `NoGeneralRoute` records `gate-refused`, because A4 added a gate that
    refuses such a plan; the same situation under A2 recorded
    `no-general-route`, because there was no gate to refuse it. The proposal
    variant is the earlier observation, so it is the first blocker and the
    decline class joins the known set. Reading only the decline class would
    split one obstruction across two clusters and blame a harness change for it.
    """
    outcome = document["outcome"]
    decline_class = outcome.get("decline_class")
    tactics = sorted({t for row in proposals for t in row.get("tactic_ids", [])})
    no_route = [row for row in proposals if row.get("route") == "none"]

    if no_route:
        detail = "+".join(sorted({t for row in no_route for t in row.get("tactic_ids", [])}))
        first = {
            "kind": "no-general-route",
            "detail": detail or "no-tactic-named",
            "source": "episode-proposal-route",
        }
        known = [first]
        if decline_class == "gate-refused":
            known.append(
                {
                    "kind": "gate-refused",
                    "detail": "the deterministic gate refuses a NoGeneralRoute plan",
                    "source": "episode-decline-class",
                }
            )
        return first, known, first["detail"]

    if decline_class == "retrieval-miss":
        first = {
            "kind": "export-missing",
            "detail": "frozen-statement-export",
            "source": "episode-decline-class",
        }
        return first, [first], "frozen-statement-export"

    if decline_class in ("budget-exhausted-before-plan", "budget-exhausted-during-plan"):
        phase = decline_class.removeprefix("budget-exhausted-")
        first = {"kind": "budget", "detail": phase, "source": "episode-decline-class"}
        return first, [first], phase

    first = {
        "kind": "unclassified",
        "detail": str(decline_class),
        "source": "episode-decline-class",
    }
    return first, [first], str(decline_class)


# ------------------------------------------------------------ decline records


def decline_record_paths() -> list[pathlib.Path]:
    paths = sorted(p for p in AUTOGENESIS.glob("*-decline-v*.json") if DECLINE_RECORD.search(p.name))
    if not paths:
        raise DeriveError(f"{AUTOGENESIS}: no producer decline records; nothing to derive from")
    return paths


def _first(node: Any, key: str) -> Any:
    """The first value under `key` anywhere in the document, or None.

    The eleven records have eleven shapes -- `observation.axiom_footprint` in
    one, `attempt.diagnostic` in another -- and each grew around the run it
    described. A keyed search is what lets one predicate read all of them
    without a per-file table, which is what "derived, not authored" requires.
    """
    if isinstance(node, dict):
        if key in node:
            return node[key]
        for value in node.values():
            found = _first(value, key)
            if found is not None:
                return found
    elif isinstance(node, list):
        for value in node:
            found = _first(value, key)
            if found is not None:
                return found
    return None


def classify_decline_record(document: dict) -> tuple[dict, str]:
    """`(blocker, coarse cluster detail)` from a record's own structure.

    Order matters and is not arbitrary. A record that reached the kernel and
    came back with a non-empty axiom footprint is an axiom-footprint finding
    even though its source also compiled; a record whose replay driver refused
    before reconstructing never had a footprint to measure. The predicates are
    therefore ordered from "got furthest" to "stopped earliest", so the blocker
    named is the one that actually stopped the run.
    """
    state = str(document.get("state", ""))

    footprint = _first(document, "axiom_footprint")
    if isinstance(footprint, list) and footprint:
        detail = "+".join(sorted(str(a) for a in footprint))
        return (
            {
                "kind": "axiom-footprint-nonempty",
                "detail": detail,
                "source": "decline-record-observation",
            },
            detail,
        )

    diagnostic = str(_first(document, "diagnostic") or "")
    if diagnostic.startswith("AUTOGENESIS_READINESS_ERROR"):
        return (
            {
                "kind": "replay-readiness-mismatch",
                "detail": diagnostic.split("|", 1)[-1],
                "source": "decline-record-observation",
            },
            "readiness-precondition",
        )

    export = document.get("export")
    if isinstance(export, dict) and export.get("declarations_exported") == 0:
        return (
            {
                "kind": "export-missing",
                "detail": str(export.get("diagnostic") or "no declarations exported"),
                "source": "decline-record-observation",
            },
            "frozen-statement-export",
        )

    driver = document.get("driver")
    if isinstance(driver, dict) and driver.get("diagnostic"):
        return (
            {
                "kind": "tooling-gate-refused",
                "detail": str(driver["diagnostic"]),
                "source": "decline-record-observation",
            },
            "producer-driver-lint",
        )

    outcome_class = str(_first(document, "outcome_class") or "")
    if outcome_class.startswith("kernel-rejection"):
        return (
            {
                "kind": "tactic-precondition-unmatched",
                "detail": outcome_class,
                "source": "decline-record-observation",
            },
            outcome_class,
        )

    blocked = _first(document, "first_blocked_operation")
    if blocked or "elaboration" in state or _first(document, "olean_created") is False:
        return (
            {
                "kind": "elaboration-blocked",
                "detail": str(blocked or state or "lean-elaboration"),
                "source": "decline-record-observation",
            },
            str(blocked or "lean-elaboration"),
        )

    return (
        {"kind": "unclassified", "detail": state or "unknown", "source": "decline-record-observation"},
        state or "unknown",
    )


# ---------------------------------------------------------------- the derivation


def derive() -> tuple[dict, list[str]]:
    held_out = held_out_ids()
    partition_of, family_of = partitions_and_families()
    must_decline = must_decline_ids()
    capabilities = overlay_capabilities()
    realizes = tactic_capabilities()

    inputs: list[dict] = []
    clusters: dict[str, dict] = {}
    breaches: list[str] = []
    unclassified: list[str] = []

    def cluster(key: str) -> dict:
        return clusters.setdefault(
            key,
            {
                "cluster_key": key,
                "first_blocker": None,
                "known": {},
                "facts": set(),
                "tactics": set(),
                "decline_classes": set(),
                "evidence": [],
                "funnel": {
                    "goal": 0,
                    "adapter": 0,
                    "producer": 0,
                    "reconstruction": 0,
                    "checker": 0,
                    "obstruction": 0,
                },
            },
        )

    def remember(entry: dict, blocker: dict) -> None:
        entry["known"].setdefault((blocker["kind"], blocker["detail"], blocker["source"]), blocker)

    funnel = {
        "goal": 0,
        "adapter": 0,
        "producer": 0,
        "reconstruction": 0,
        "checker": 0,
        "obstruction": 0,
        "episodes_read": 0,
        "episodes_contributing": 0,
    }

    for path in episode_paths():
        document = load_json(path)
        digest = sha256_file(path)
        inputs.append({"path": repo_relative(path), "sha256": digest, "kind": "episode"})
        stages = episode_funnel(document)
        for stage, value in stages.items():
            funnel[stage] += value
        funnel["episodes_read"] += 1
        if document["outcome"]["verdict"] == "proved":
            continue
        funnel["episodes_contributing"] += 1
        proposals = episode_proposals(path, document)
        first, known, detail = classify_episode(document, proposals)
        if first["kind"] == "unclassified":
            unclassified.append(f"{repo_relative(path)}: decline class {first['detail']!r}")
        key = f"{first['kind']}|{detail}"
        entry = cluster(key)
        entry["first_blocker"] = entry["first_blocker"] or dict(first, observed_in=repo_relative(path))
        for blocker in known:
            remember(entry, dict(blocker, observed_in=repo_relative(path)))
        fact_id = document["selection"]["fact_id"]
        blind_selection = fact_id in held_out
        if blind_selection:
            # Recorded WITHOUT echoing the id, and the evidence row below omits
            # it too. `axeyum.agent.models.assert_referenceable` makes the same
            # choice for the same reason: a held-out id in a refusal message is
            # a held-out id in a log. The generic string walk over the rendered
            # bytes is the backstop, not the first line.
            breaches.append(f"{repo_relative(path)}: selection names a held-out fact")
        elif fact_id not in must_decline:
            entry["facts"].add(fact_id)
        entry["tactics"].update(t for row in proposals for t in row.get("tactic_ids", []))
        entry["decline_classes"].add(document["outcome"].get("decline_class"))
        entry["evidence"].append(
            {
                "path": repo_relative(path),
                "sha256": digest,
                "kind": "episode",
                **({} if blind_selection else {"fact_id": fact_id}),
                "decline_class": document["outcome"].get("decline_class"),
            }
        )
        for stage, value in stages.items():
            entry["funnel"][stage] += value

    for path in decline_record_paths():
        document = load_json(path)
        digest = sha256_file(path)
        inputs.append({"path": repo_relative(path), "sha256": digest, "kind": "decline-record"})
        blocker, detail = classify_decline_record(document)
        if blocker["kind"] == "unclassified":
            unclassified.append(f"{repo_relative(path)}: state {blocker['detail']!r}")
        key = f"{blocker['kind']}|{detail}"
        entry = cluster(key)
        entry["first_blocker"] = entry["first_blocker"] or dict(blocker, observed_in=repo_relative(path))
        remember(entry, dict(blocker, observed_in=repo_relative(path)))
        for fact_id in sorted(set(keyed_fact_ids(document))):
            if fact_id in held_out:
                breaches.append(f"{repo_relative(path)}: names a held-out fact")
            elif fact_id not in must_decline:
                entry["facts"].add(fact_id)
        entry["evidence"].append(
            {"path": repo_relative(path), "sha256": digest, "kind": "decline-record"}
        )

    for path in (NURSERY, OVERLAY, CATALOG, MUST_DECLINE):
        inputs.append({"path": repo_relative(path), "sha256": sha256_file(path), "kind": "manifest"})

    if unclassified:
        raise DeriveError(
            "decline evidence matched no predicate; a new shape must be classified rather "
            "than dropped: " + "; ".join(sorted(unclassified))
        )

    entities: list[dict] = []
    links: list[dict] = []
    for key in sorted(clusters):
        entry = clusters[key]
        first = entry["first_blocker"]
        facts = sorted(entry["facts"])
        counts: dict[str, int] = {}
        families: set[str] = set()
        for fact_id in facts:
            name = partition_of.get(fact_id, "unregistered")
            counts[name] = counts.get(name, 0) + 1
            families.add(family_of.get(fact_id, "unregistered"))
        capability_id, reason = CANDIDATES[first["kind"]]
        obstruction = {
            "id": cluster_id(key),
            "kind": "obstruction",
            "title": f"{first['kind']}: {first['detail']}",
            "cluster_key": key,
            "decline_classes": sorted(entry["decline_classes"], key=lambda v: (v is not None, v)),
            "first_blocker": first,
            "known_blockers": [entry["known"][k] for k in sorted(entry["known"])],
            "population": {
                "fact_ids": facts,
                "partitions": dict(sorted(counts.items())),
                "families": sorted(families),
            },
            "facts_blocked": len(facts),
            "tactic_ids": sorted(entry["tactics"]),
            "candidate_capability": {
                "id": capability_id,
                "exists": capability_id in capabilities,
                "reason": reason,
            },
            "resolution": {"commit": None, "before": entry["funnel"], "after": None},
            "evidence": sorted(entry["evidence"], key=lambda row: row["path"]),
            "assurance": "mechanically-observed",
            "status": "open",
        }
        entities.append(obstruction)
        links.extend(links_for(obstruction, entry, realizes))

    document = {
        "schema_version": 1,
        "kind": "axeyum-obstruction-graph",
        "generated_by": "scripts/gen-obstruction-graph.py",
        "inputs": sorted(inputs, key=lambda row: row["path"]),
        "namespaces": NAMESPACES,
        "relation_types": RELATION_TYPES,
        "funnel": funnel,
        "entities": entities,
        "links": sorted(links, key=lambda row: row["id"]),
    }
    return document, breaches


def links_for(obstruction: dict, entry: dict, realizes: dict[str, str]) -> list[dict]:
    """`blocked-by` from every fact, tactic and realized capability to the cluster.

    The capability endpoints are derived, not chosen: a tactic's `realizes` id
    comes from the tactic catalog, so a capability appears here exactly when a
    tactic that names it was in flight when the obstruction was hit. That is a
    claim about what was BLOCKED, and it is separate from
    `candidate_capability`, which is a claim about what would REMOVE the block.
    """
    target = {"namespace": "axeyum-obstruction", "kind": "obstruction", "id": obstruction["id"]}
    sources = sorted(obstruction["evidence"], key=lambda row: row["path"])
    provenance = {
        "method": "mechanically-observed",
        "sources": sorted({row["path"] for row in sources}),
    }
    rows = []
    for fact_id in obstruction["population"]["fact_ids"]:
        rows.append(
            {
                "id": link_id("blocked-by", fact_id, obstruction["id"]),
                "relation": "blocked-by",
                "source": {"namespace": "axeyum-fact", "kind": "fact", "id": fact_id},
                "target": target,
                "assurance": "mechanically-observed",
                "status": "open",
                "reason": (
                    f"{fact_id} is in the measured population of {obstruction['id']}; the "
                    f"first observed blocker was {obstruction['first_blocker']['kind']}."
                ),
                "provenance": provenance,
                "evidence": provenance["sources"],
            }
        )
    for tactic_id in obstruction["tactic_ids"]:
        rows.append(
            {
                "id": link_id("blocked-by", tactic_id, obstruction["id"]),
                "relation": "blocked-by",
                "source": {"namespace": "axeyum-tactic", "kind": "tactic", "id": tactic_id},
                "target": target,
                "assurance": "mechanically-observed",
                "status": "open",
                "reason": (
                    f"{tactic_id} was the tactic a plan named when {obstruction['id']} was "
                    f"observed. This records what was in flight, not that the tactic is wrong."
                ),
                "provenance": provenance,
                "evidence": provenance["sources"],
            }
        )
    for capability_id in sorted({realizes[t] for t in obstruction["tactic_ids"] if t in realizes}):
        rows.append(
            {
                "id": link_id("blocked-by", capability_id, obstruction["id"]),
                "relation": "blocked-by",
                "source": {
                    "namespace": "axeyum-knowledge",
                    "kind": "capability",
                    "id": capability_id,
                },
                "target": target,
                "assurance": "mechanically-observed",
                "status": "open",
                "reason": (
                    f"{capability_id} is what the tactic catalog says the in-flight tactics "
                    f"realize, so this capability did not reach the population of "
                    f"{obstruction['id']}."
                ),
                "provenance": provenance,
                "evidence": provenance["sources"],
            }
        )
    return rows


NAMESPACES = [
    {
        "id": "axeyum-obstruction",
        "endpoint_kinds": ["obstruction"],
        "resolution": "sidecar-entity",
        "notes": (
            "Obstruction ids are defined by THIS document. The overlay declares "
            "`obstruction` as an entity kind and has no obstruction entities."
        ),
    },
    {
        "id": "axeyum-fact",
        "endpoint_kinds": ["fact"],
        "resolution": "local-required",
        "path": "artifacts/facts",
        "notes": "Every id must resolve to artifacts/facts/F-<slug>.json.",
    },
    {
        "id": "axeyum-tactic",
        "endpoint_kinds": ["tactic"],
        "resolution": "local-required",
        "path": "artifacts/autogenesis/tactic-catalog-v1.json",
        "notes": (
            "`tactic` is NOT an overlay entity kind. A link with this namespace is a "
            "sidecar view and cannot be copied into the overlay."
        ),
    },
    {
        "id": "axeyum-knowledge",
        "endpoint_kinds": ["capability"],
        "resolution": "overlay-required",
        "path": "artifacts/autogenesis/knowledge-overlay-v1.json",
        "notes": (
            "A `K:` id must resolve in the overlay unless it is spelled `K:proposed-...`, "
            "which is how a candidate says out loud that it does not exist yet."
        ),
    },
]

RELATION_TYPES = [
    {
        "id": "blocked-by",
        "source_kinds": ["fact", "tactic", "capability", "operation"],
        "target_kinds": ["obstruction"],
        "semantics": (
            "The source was observed not to progress because of the target obstruction. "
            "This is an observation about one or more committed runs. It is NOT a claim "
            "that the source is unreachable, that the fact is false, or that removing the "
            "obstruction would close it."
        ),
    }
]


def render(document: dict) -> str:
    return json.dumps(document, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def held_out_in_text(text: str, held_out: set[str]) -> list[str]:
    """A generic walk over the RENDERED bytes, not over the structured fields.

    Both are checked because a field-specific guard is bypassable by the next
    field somebody adds -- the reason `check-autogenesis-holdout-isolation.py`
    string-walks whole artifacts rather than reading `applicability.fact_ids`.
    """
    return sorted(ident for ident in held_out if ident in text)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="fail when the committed file is stale")
    parser.add_argument("--output", type=pathlib.Path, default=OUTPUT)
    args = parser.parse_args(argv)

    try:
        document, breaches = derive()
    except DeriveError as error:
        print(f"OBSTRUCTIONS_ERROR|{error}", file=sys.stderr)
        return 1

    rendered = render(document)
    try:
        blind = held_out_ids()
    except DeriveError as error:
        print(f"OBSTRUCTIONS_ERROR|{error}", file=sys.stderr)
        return 1
    breaches.extend(
        f"rendered document names held-out fact {ident}"
        for ident in held_out_in_text(rendered, blind)
    )
    if breaches:
        for breach in sorted(set(breaches)):
            print(f"OBSTRUCTIONS_ERROR|{breach}", file=sys.stderr)
        return 1

    entities = document["entities"]
    if not entities:
        print(
            "OBSTRUCTIONS_ERROR|no obstruction was derived; a census that found nothing was "
            "pointed at nothing",
            file=sys.stderr,
        )
        return 1

    if args.check:
        if not args.output.exists() or args.output.read_text(encoding="utf-8") != rendered:
            print(
                "OBSTRUCTIONS_ERROR|the committed obstruction graph is stale; run "
                "scripts/gen-obstruction-graph.py",
                file=sys.stderr,
            )
            return 1
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")

    facts_blocked = len({f for e in entities for f in e["population"]["fact_ids"]})
    largest = max(entities, key=lambda e: (e["facts_blocked"], len(e["evidence"]), e["id"]))
    from_episodes = sum(1 for row in document["inputs"] if row["kind"] == "episode")
    from_records = sum(1 for row in document["inputs"] if row["kind"] == "decline-record")
    print(
        "OBSTRUCTIONS|"
        f"entities={len(entities)}|"
        f"links={len(document['links'])}|"
        f"facts_blocked={facts_blocked}|"
        f"from_episodes={from_episodes}|"
        f"from_decline_records={from_records}|"
        f"largest_cluster={largest['id']}:{largest['facts_blocked']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
