#!/usr/bin/env python3
"""Validate the derived obstruction graph. The exit status depends on the finding.

`scripts/gen-obstruction-graph.py` derives the graph; this file is the
independent re-validator, and the two are deliberately not the same program.
The generator can be wrong in exactly the way this repository has been bitten by
before -- a certificate that does not carry every distinction its producer makes
-- so this checker re-derives what the document claims rather than reading it:

* every obstruction id is **recomputed** from its own `cluster_key`, so an id
  that was edited by hand, or a cluster key that was edited without
  regenerating, is caught without diffing the whole file;
* every `evidence[].sha256` is **re-hashed from disk**, so a row citing bytes
  nobody can reproduce is an error rather than a footnote;
* every `candidate_capability.exists` is **re-measured** against the knowledge
  overlay, because that flag is the difference between "we have this and have
  not aimed it" and "somebody has to build it";
* held-out ids are refused **twice** -- once over the structured populations and
  once as a generic walk over every string in the document -- for the reason
  `check-autogenesis-holdout-isolation.py` gives: operations already carried
  fact ids at three distinct JSON paths, so a field-specific guard was
  bypassable the day it was written.

FAIL-CLOSED throughout. A document with zero entities, an unreadable nursery, or
an empty held-out population is an error: a validator whose subject has vanished
prints the same "no violations" as one that works.

`jsonschema` is used when it happens to be installed and the essential structural
rules are checked without it, exactly as `validate-autogenesis-knowledge.py`
does -- no gate in `just check` may require a network install.

Stdlib only.
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
DEFAULT_GRAPH = ROOT / "artifacts/autogenesis/obstruction-graph-v1.json"
SCHEMA = ROOT / "artifacts/ontology/obstruction-graph.schema.json"
OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"
CATALOG = ROOT / "artifacts/autogenesis/tactic-catalog-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
FACTS = ROOT / "artifacts/facts"

TOP_KEYS = {
    "schema_version",
    "kind",
    "generated_by",
    "inputs",
    "namespaces",
    "relation_types",
    "funnel",
    "entities",
    "links",
}

#: The ceiling, and the whole point of it. `formal-derived`,
#: `independently-checked`, `registry-derived` and `human-reviewed` are overlay
#: values and are NOT admissible here: an obstruction is an observation about a
#: run, and no run in this graph was checked by a kernel, a checker, a registry
#: or a person.
ASSURANCE = {"mechanically-observed", "heuristic", "proposed"}
METHOD = "mechanically-observed"
STATUS = {"open", "mitigated", "resolved"}

DECLINE_CLASSES = {
    None,
    "unsupported-semantics",
    "missing-lemma",
    "missing-plan-rule",
    "missing-certificate",
    "representation-explosion",
    "resource-exhaustion",
    "retrieval-miss",
    "formalization-mismatch",
    "operational-failure",
    "no-general-route",
    "gate-refused",
    "supervisor-denied",
    "budget-exhausted-before-plan",
    "budget-exhausted-during-plan",
}

ENTITY_KEYS = {
    "id",
    "kind",
    "title",
    "cluster_key",
    "decline_classes",
    "first_blocker",
    "known_blockers",
    "population",
    "facts_blocked",
    "tactic_ids",
    "candidate_capability",
    "resolution",
    "evidence",
    "assurance",
    "status",
}
LINK_KEYS = {
    "id",
    "relation",
    "source",
    "target",
    "assurance",
    "status",
    "reason",
    "provenance",
    "evidence",
}
FUNNEL_STAGES = ("goal", "adapter", "producer", "reconstruction", "checker", "obstruction")

OBSTRUCTION_ID = re.compile(r"^O:[a-z0-9]+(?:-[a-z0-9]+)*$")
FACT_ID = re.compile(r"^F:[a-z0-9]+(?:-[a-z0-9]+)*$")
PROPOSED_CAPABILITY = "K:proposed-"


class ValidationError(Exception):
    """Raised when the checker's own subject is unusable. Never a pass."""


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValidationError(f"{path}: cannot read JSON: {error}") from error


def cluster_id(cluster_key: str) -> str:
    kind = cluster_key.split("|", 1)[0]
    return f"O:{kind}-{hashlib.sha256(cluster_key.encode('utf-8')).hexdigest()[:8]}"


def walk_strings(node: Any):
    if isinstance(node, dict):
        for value in node.values():
            yield from walk_strings(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk_strings(value)
    elif isinstance(node, str):
        yield node


def held_out_ids() -> set[str]:
    manifest = load_json(NURSERY)
    entries = manifest.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValidationError(f"{NURSERY}: no entries; the isolation guard has no subject")
    held = {
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict) and entry.get("partition") == "held-out"
    }
    if not held:
        raise ValidationError(f"{NURSERY}: held-out population is empty; refusing a vacuous guard")
    return held


def overlay_capabilities() -> set[str]:
    return {
        entity["id"]
        for entity in load_json(OVERLAY).get("entities", [])
        if isinstance(entity, dict) and entity.get("kind") == "capability"
    }


def catalog_tactics() -> set[str]:
    return {
        row["id"]
        for row in load_json(CATALOG).get("tactics", [])
        if isinstance(row, dict) and "id" in row
    }


def schema_check(document: Any, errors: list[str]) -> None:
    """Draft 2020-12 when available; the essential rules without it."""
    try:
        import jsonschema  # type: ignore[import-not-found]
    except ImportError:
        jsonschema = None
    if jsonschema is not None:
        schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
        validator = jsonschema.Draft202012Validator(schema)
        for error in sorted(validator.iter_errors(document), key=lambda e: list(e.path)):
            where = ".".join(str(part) for part in error.path) or "<root>"
            errors.append(f"schema {where}: {error.message}")
        return
    if not isinstance(document, dict):
        errors.append("obstruction graph root must be an object")
        return
    if set(document) != TOP_KEYS:
        errors.append(f"root keys differ: got {sorted(document)}, expected {sorted(TOP_KEYS)}")
    if document.get("schema_version") != 1:
        errors.append("schema_version must be 1")
    if document.get("kind") != "axeyum-obstruction-graph":
        errors.append("kind must be axeyum-obstruction-graph")
    for key in ("inputs", "namespaces", "relation_types", "entities", "links"):
        if not isinstance(document.get(key), list):
            errors.append(f"{key} must be an array")


def validate_document(document: Any, root: pathlib.Path = ROOT) -> list[str]:
    errors: list[str] = []
    schema_check(document, errors)
    # The local rules run EVEN WHEN the schema complained, and that is not
    # tidiness. `jsonschema` is installed on some hosts and not others, and a
    # rule that only executes where the library is absent is a rule nobody
    # measures: every mutation control for it would report SURVIVED on a
    # developer box and killed in CI, or the reverse. The two layers overlap on
    # purpose and each must be able to fail on its own.
    if not isinstance(document, dict):
        return errors
    entities = document.get("entities")
    links = document.get("links")
    if not isinstance(entities, list) or not isinstance(links, list):
        errors.append("entities and links must both be arrays; nothing further can be checked")
        return errors

    if not entities:
        errors.append("the graph declares no obstruction; a validator with no subject is not a pass")
        return errors

    blind = held_out_ids()
    capabilities = overlay_capabilities()
    tactics = catalog_tactics()

    seen_ids: set[str] = set()
    evidence_checked = 0

    for entity in entities:
        where = entity.get("id", "<no id>")
        if set(entity) != ENTITY_KEYS:
            errors.append(f"{where}: entity keys differ: got {sorted(entity)}")
            continue
        ident = entity["id"]
        if not OBSTRUCTION_ID.match(ident):
            errors.append(f"{where}: obstruction id is not O:<slug>")
        if ident in seen_ids:
            errors.append(f"{where}: duplicate obstruction id")
        seen_ids.add(ident)

        expected = cluster_id(entity["cluster_key"])
        if ident != expected:
            errors.append(
                f"{where}: id does not re-derive from cluster_key {entity['cluster_key']!r} "
                f"(expected {expected}); the id is a digest, not a name"
            )

        if entity["assurance"] not in ASSURANCE:
            errors.append(
                f"{where}: assurance {entity['assurance']!r} is above the ceiling; an "
                f"obstruction is observed, never checked or reviewed"
            )
        if entity["status"] not in STATUS:
            errors.append(f"{where}: unknown status {entity['status']!r}")

        for value in entity["decline_classes"]:
            if value not in DECLINE_CLASSES:
                errors.append(f"{where}: decline class {value!r} is not in the v2 episode enum")

        first = entity["first_blocker"]
        known = entity["known_blockers"]
        if not known:
            errors.append(f"{where}: known_blockers is empty; a first blocker is always known")
        elif not any(
            row["kind"] == first["kind"] and row["detail"] == first["detail"] for row in known
        ):
            errors.append(
                f"{where}: first_blocker is absent from known_blockers; the complete set must "
                f"contain the first observation, not replace it"
            )

        population = entity["population"]
        fact_ids = population["fact_ids"]
        for fact_id in fact_ids:
            if not FACT_ID.match(fact_id):
                errors.append(f"{where}: {fact_id!r} is not a fact id")
                continue
            if fact_id in blind:
                errors.append(f"{where}: population names a held-out fact")
                continue
            path = root / "artifacts/facts" / (fact_id.replace("F:", "F-") + ".json")
            if not path.is_file():
                errors.append(f"{where}: population fact {fact_id} does not resolve in the ledger")
        if "held-out" in population["partitions"]:
            errors.append(f"{where}: partitions count a held-out row")
        if entity["facts_blocked"] != len(fact_ids):
            errors.append(
                f"{where}: facts_blocked={entity['facts_blocked']} but the population holds "
                f"{len(fact_ids)}"
            )

        for tactic_id in entity["tactic_ids"]:
            if tactic_id not in tactics:
                errors.append(f"{where}: tactic {tactic_id} does not resolve in the tactic catalog")

        candidate = entity["candidate_capability"]
        exists = candidate["id"] in capabilities
        if candidate["exists"] != exists:
            errors.append(
                f"{where}: candidate_capability.exists={candidate['exists']} but the overlay "
                f"{'has' if exists else 'does not have'} {candidate['id']}"
            )
        if not exists and not candidate["id"].startswith(PROPOSED_CAPABILITY):
            errors.append(
                f"{where}: {candidate['id']} is not in the overlay and is not spelled "
                f"K:proposed-...; a wish must say so in its own id"
            )

        resolution = entity["resolution"]
        if resolution["commit"] is None and resolution["after"] is not None:
            errors.append(
                f"{where}: an after-funnel without a resolution commit is a before/after that "
                f"was never measured twice"
            )
        for stage in FUNNEL_STAGES:
            if stage not in resolution["before"]:
                errors.append(f"{where}: before-funnel is missing stage {stage!r}")

        if not entity["evidence"]:
            errors.append(f"{where}: no evidence; an obstruction nobody observed is prose")
        for row in entity["evidence"]:
            path = root / row["path"]
            if not path.is_file():
                errors.append(f"{where}: evidence {row['path']} is not on disk")
                continue
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if digest != row["sha256"]:
                errors.append(
                    f"{where}: evidence {row['path']} hashes to {digest[:12]}..., recorded "
                    f"{row['sha256'][:12]}..."
                )
            evidence_checked += 1

    relations = {row["id"]: row for row in document.get("relation_types", [])}
    link_ids: set[str] = set()
    for link in links:
        where = link.get("id", "<no id>")
        required = LINK_KEYS - {"evidence"}
        if (set(link) - LINK_KEYS) or not required.issubset(link):
            errors.append(f"{where}: link keys differ: got {sorted(link)}")
            continue
        if where in link_ids:
            errors.append(f"{where}: duplicate link id")
        link_ids.add(where)
        relation = relations.get(link["relation"])
        if relation is None:
            errors.append(f"{where}: relation {link['relation']!r} is not declared")
            continue
        if link["source"]["kind"] not in relation["source_kinds"]:
            errors.append(
                f"{where}: {link['source']['kind']} is not a source kind of {link['relation']}"
            )
        if link["target"]["kind"] not in relation["target_kinds"]:
            errors.append(
                f"{where}: {link['target']['kind']} is not a target kind of {link['relation']}"
            )
        if link["target"]["id"] not in seen_ids:
            errors.append(f"{where}: target {link['target']['id']} is not an obstruction here")
        if link["assurance"] not in ASSURANCE:
            errors.append(f"{where}: assurance {link['assurance']!r} is above the ceiling")
        if link["provenance"]["method"] != METHOD:
            errors.append(
                f"{where}: provenance method {link['provenance']['method']!r}; every row in "
                f"this file is mechanically observed and nothing else"
            )
        source = link["source"]
        if source["kind"] == "fact":
            if source["id"] in blind:
                errors.append(f"{where}: link source is a held-out fact")
            elif not (root / "artifacts/facts" / (source["id"].replace("F:", "F-") + ".json")).is_file():
                errors.append(f"{where}: link source fact {source['id']} does not resolve")
        elif source["kind"] == "tactic" and source["id"] not in tactics:
            errors.append(f"{where}: link source tactic {source['id']} does not resolve")
        elif source["kind"] == "capability" and source["id"] not in capabilities:
            if not source["id"].startswith(PROPOSED_CAPABILITY):
                errors.append(f"{where}: link source capability {source['id']} is not in the overlay")

    # SUBSTRING, not equality. A held-out id embedded in a `reason`, a blocker
    # `detail` copied verbatim out of a decline record's diagnostic, or a title
    # is as much a breach as one sitting in `population.fact_ids` -- and it is
    # the case the field-specific guards above structurally cannot see.
    strings = list(walk_strings(document))
    leaked = sorted(ident for ident in blind if any(ident in text for text in strings))
    if leaked:
        errors.append(f"{len(leaked)} held-out fact id(s) appear as strings in this document")

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("path", nargs="?", type=pathlib.Path, default=DEFAULT_GRAPH)
    args = parser.parse_args(argv)
    try:
        document = load_json(args.path)
        errors = validate_document(document)
    except ValidationError as error:
        print(f"OBSTRUCTION_GRAPH_ERROR|{error}", file=sys.stderr)
        return 1
    for error in errors:
        print(f"OBSTRUCTION_GRAPH_ERROR|{error}", file=sys.stderr)
    if errors:
        return 1
    facts = len({f for e in document["entities"] for f in e["population"]["fact_ids"]})
    evidence = sum(len(e["evidence"]) for e in document["entities"])
    print(
        "OBSTRUCTION_GRAPH_OK|"
        f"entities={len(document['entities'])}|"
        f"links={len(document['links'])}|"
        f"facts_blocked={facts}|"
        f"evidence_rehashed={evidence}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
