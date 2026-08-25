#!/usr/bin/env python3
"""Validate the tactic catalog: the proof-strategy vocabulary a plan resolves against.

A catalog of names is not a capability inventory, and a registry where every
entry matches exactly one goal is a dispatch table rather than a producer
(`docs/autogenesis/228-capsule-lane-retrospective.md`).  So this validator does
two jobs, and the second is the one that can fail on a healthy-looking file:

1.  *Binding.*  Every claim a tactic makes about the code is re-derived from the
    code.  ``implemented_by.path`` must exist and contain ``symbol``; every
    ``decline_reasons`` entry must be a real variant of THAT file's own
    ``DeclineReason`` enum; every ``budget`` constant must equal the ``const``
    in THAT file (aliases such as ``const MAX_ABSURD_HYPOTHESES: usize =
    MAX_BINDERS;`` are resolved); ``realizes`` must resolve to a ``capability``
    entity in the knowledge overlay; ``uses_technique`` names a technique and is
    NOT resolved anywhere (ADR-0553 -- it used to carry a sibling repository's
    pinned commit and be stat-ed against that checkout).

2.  *The census.*  It prints ``TACTIC_CATALOG|...`` and **fails** when
    ``distinct_precondition_shapes < 2`` (every entry matching one goal shape is
    a dispatch table) or when any tactic has zero reach rows (a tactic with no
    measured accepted or declined goal is a name, not a capability).  The exit
    status depends on what was found, never on the run having completed.

The structural check is stdlib-only and is the gate.  Draft 2020-12 validation
against the published schema runs only under ``--with-jsonschema``, and
deliberately not by default: a gate whose strictness depends on whether an
optional package happens to be installed on this host is the aggregate form of
the "running 0 tests ... ok" trap, and ``scripts/`` may not depend on
third-party packages at all.  ``scripts/tests/test_validate_tactic_catalog.py``
runs the published-schema pass over the committed catalog so the two cannot
drift apart unnoticed.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CATALOG = ROOT / "artifacts/autogenesis/tactic-catalog-v1.json"
SCHEMA = ROOT / "artifacts/ontology/tactic-catalog.schema.json"
OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"

TOP_KEYS_REQUIRED = {"schema_version", "kind", "tactics"}
TOP_KEYS_ALLOWED = TOP_KEYS_REQUIRED | {"notes"}

TACTIC_KEYS = {
    "id", "title", "kind", "precondition", "move", "residual", "budget",
    "decline_reasons", "implemented_by", "realizes", "uses_technique",
    "reach", "assurance", "status",
}
TACTIC_KINDS = {
    "closure", "induction", "rewrite", "lemma-splice",
    "elimination", "case-split", "generalization", "combinator",
}
ASSURANCE = {
    "formal-derived", "independently-checked", "registry-derived",
    "mechanically-observed", "human-reviewed", "heuristic", "proposed",
}
STATUS = {"active", "candidate", "deprecated"}

# The predicate vocabulary, mirrored from the schema: kind -> (required args,
# optional args, {arg: allowed values}).  A predicate kind that is not in this
# table is rejected, which is what keeps preconditions typed rather than
# free-form -- there is deliberately no way to write a regex over a name.
PREDICATES: dict[str, tuple[set[str], set[str], dict[str, set[Any]]]] = {
    "goal-head": ({"head"}, set(), {"head": {"Eq", "Iff", "any-prop"}}),
    "sides-definitionally-equal": ({"value"}, set(), {"value": {True, False}}),
    "binder-shape": (
        {"shape"}, set(), {"shape": {"zero-succ", "ordinary-pi", "hypothesis-pi"}},
    ),
    "hypothesis-family": (
        {"family", "index"}, {"parameter"},
        {
            "family": {"le-shaped", "eq-shaped"},
            "index": {"zero", "succ", "any"},
            "parameter": {"zero", "succ", "any"},
        },
    ),
    "hypothesis-state": (
        {"state"}, set(), {"state": {"available", "stuck", "absent"}},
    ),
    "occurrence-embeds": (
        {"needle", "haystack", "via"}, set(),
        {
            "needle": {"hypothesis-lhs", "hypothesis-rhs", "candidate-argument"},
            "haystack": {"goal-lhs-whnf", "goal-rhs-whnf", "expected-argument"},
            "via": {"kabstract-occurrences", "app-spine"},
        },
    ),
    "residual-gap-shape": (
        {"shape"}, set(),
        {"shape": {
            "single-argument-diff",
            "multi-argument-diff-same-head",
            "collapsed-occurrence-site",
        }},
    ),
    "spine-argument-matches": (
        {"position", "target"}, set(),
        {"position": {"any-top-level"}, "target": {"goal-rhs"}},
    ),
    "head-unfolds": (
        {"via", "to"}, set(), {"via": {"whnf-delta"}, "to": {"Eq", "Iff"}},
    ),
}

TACTIC_ID = re.compile(r"^T:[a-z0-9]+(?:-[a-z0-9]+)*$")
CAPABILITY_ID = re.compile(r"^K:[a-z0-9]+(?:-[a-z0-9]+)*$")
TECHNIQUE_ID = re.compile(r"^TQ:[a-z0-9]+(?:-[a-z0-9]+)*$")
CONST_DECL = re.compile(
    r"^[ \t]*(?:pub[ \t]+)?const[ \t]+([A-Z][A-Z0-9_]*)[ \t]*:[ \t]*[A-Za-z0-9_]+[ \t]*=[ \t]*([^;]+);",
    re.MULTILINE,
)
DECLINE_ENUM = re.compile(r"enum[ \t]+DeclineReason[ \t]*\{(.*?)\n\}", re.DOTALL)
VARIANT = re.compile(r"^[ \t]*([A-Z][A-Za-z0-9]*)[ \t]*(?:\([^)]*\))?[ \t]*,", re.MULTILINE)


def err(errors: list[str], rule: str, detail: str) -> None:
    errors.append(f"{rule}|{detail}")


# --------------------------------------------------------------------------
# Structural validation (stdlib; always runs)
# --------------------------------------------------------------------------

def check_predicate(predicate: Any, where: str, errors: list[str]) -> None:
    if not isinstance(predicate, dict):
        err(errors, "schema", f"{where}: predicate must be an object")
        return
    if set(predicate) != {"kind", "args"}:
        err(errors, "schema", f"{where}: predicate keys must be exactly kind, args")
        return
    kind = predicate["kind"]
    if kind not in PREDICATES:
        err(errors, "schema", f"{where}: unknown predicate kind {kind!r}")
        return
    required, optional, values = PREDICATES[kind]
    args = predicate["args"]
    if not isinstance(args, dict):
        err(errors, "schema", f"{where}: predicate args must be an object")
        return
    missing = required - set(args)
    if missing:
        err(errors, "schema", f"{where}: predicate {kind} missing args {sorted(missing)}")
    extra = set(args) - required - optional
    if extra:
        err(errors, "schema", f"{where}: predicate {kind} has unknown args {sorted(extra)}")
    for key, value in args.items():
        allowed = values.get(key)
        if allowed is not None and not any(value == item and type(value) is type(item) for item in allowed):
            err(errors, "schema", f"{where}: predicate {kind} arg {key}={value!r} is outside its vocabulary")


def check_structure(doc: Any, errors: list[str]) -> None:
    if not isinstance(doc, dict):
        err(errors, "schema", "catalog root must be an object")
        return
    missing = TOP_KEYS_REQUIRED - set(doc)
    if missing:
        err(errors, "schema", f"root is missing {sorted(missing)}")
    extra = set(doc) - TOP_KEYS_ALLOWED
    if extra:
        err(errors, "schema", f"root has unknown keys {sorted(extra)}")
    if doc.get("schema_version") != 1:
        err(errors, "schema", "schema_version must be 1")
    if doc.get("kind") != "axeyum-tactic-catalog":
        err(errors, "schema", "kind must be axeyum-tactic-catalog")
    tactics = doc.get("tactics")
    if not isinstance(tactics, list) or not tactics:
        err(errors, "schema", "tactics must be a non-empty array")
        return
    for index, tactic in enumerate(tactics):
        check_tactic_structure(tactic, index, errors)


def check_tactic_structure(tactic: Any, index: int, errors: list[str]) -> None:
    where = f"tactics[{index}]"
    if not isinstance(tactic, dict):
        err(errors, "schema", f"{where}: tactic must be an object")
        return
    ident = tactic.get("id")
    if isinstance(ident, str):
        where = f"tactic {ident}"
        if not TACTIC_ID.fullmatch(ident):
            err(errors, "schema", f"{where}: id must match T:<slug>")
    missing = TACTIC_KEYS - set(tactic)
    if missing:
        err(errors, "schema", f"{where}: missing {sorted(missing)}")
    extra = set(tactic) - TACTIC_KEYS
    if extra:
        err(errors, "schema", f"{where}: unknown keys {sorted(extra)}")
    if tactic.get("kind") not in TACTIC_KINDS:
        err(errors, "schema", f"{where}: kind {tactic.get('kind')!r} is not a tactic kind")
    if tactic.get("assurance") not in ASSURANCE:
        err(errors, "schema", f"{where}: assurance {tactic.get('assurance')!r} is not in the overlay enum")
    if tactic.get("status") not in STATUS:
        err(errors, "schema", f"{where}: status {tactic.get('status')!r} is not a status")
    if not isinstance(tactic.get("title"), str) or not tactic.get("title"):
        err(errors, "schema", f"{where}: title must be a non-empty string")

    precondition = tactic.get("precondition")
    if not isinstance(precondition, dict) or set(precondition) != {"description", "structural"}:
        err(errors, "schema", f"{where}: precondition needs exactly description and structural")
    else:
        structural = precondition["structural"]
        if not isinstance(structural, dict) or set(structural) != {"all_of"}:
            err(errors, "schema", f"{where}: precondition.structural needs exactly all_of")
        elif not isinstance(structural["all_of"], list) or not structural["all_of"]:
            err(errors, "schema", f"{where}: precondition.structural.all_of must be non-empty")
        else:
            for position, predicate in enumerate(structural["all_of"]):
                check_predicate(predicate, f"{where}.all_of[{position}]", errors)

    move = tactic.get("move")
    if not isinstance(move, dict) or set(move) != {"description", "kernel_primitives"}:
        err(errors, "schema", f"{where}: move needs exactly description and kernel_primitives")
    elif not isinstance(move["kernel_primitives"], list) or not move["kernel_primitives"]:
        err(errors, "schema", f"{where}: move.kernel_primitives must be a non-empty array")

    residual = tactic.get("residual")
    if not isinstance(residual, dict) or set(residual) != {"description", "shape", "measure"}:
        err(errors, "schema", f"{where}: residual needs exactly description, shape and measure")

    budget = tactic.get("budget")
    if not isinstance(budget, dict) or not budget:
        err(errors, "schema", f"{where}: budget must be a non-empty object")
    else:
        for name, value in budget.items():
            if not re.fullmatch(r"[A-Z][A-Z0-9_]*", name):
                err(errors, "schema", f"{where}: budget name {name!r} is not a Rust constant name")
            if not isinstance(value, int) or isinstance(value, bool):
                err(errors, "schema", f"{where}: budget {name} must be an integer")

    reasons = tactic.get("decline_reasons")
    if not isinstance(reasons, list) or not reasons:
        err(errors, "schema", f"{where}: decline_reasons must be a non-empty array")

    implemented_by = tactic.get("implemented_by")
    if not isinstance(implemented_by, dict) or set(implemented_by) != {"crate", "path", "symbol"}:
        err(errors, "schema", f"{where}: implemented_by needs exactly crate, path and symbol")

    if not isinstance(tactic.get("realizes"), str) or not CAPABILITY_ID.fullmatch(tactic.get("realizes", "")):
        err(errors, "schema", f"{where}: realizes must be a K: capability id")

    technique = tactic.get("uses_technique")
    if not isinstance(technique, dict) or set(technique) != {"id"}:
        err(errors, "schema", f"{where}: uses_technique needs exactly id (ADR-0553: no source, no revision)")
    else:
        if not TECHNIQUE_ID.fullmatch(str(technique.get("id"))):
            err(errors, "schema", f"{where}: uses_technique.id must be a TQ: id")

    reach = tactic.get("reach")
    if not isinstance(reach, dict) or set(reach) != {"accepted_goals", "declined_goals"}:
        err(errors, "schema", f"{where}: reach needs exactly accepted_goals and declined_goals")
        return
    for row in reach.get("accepted_goals") or []:
        if not isinstance(row, dict) or not row.get("goal") or not row.get("evidence"):
            err(errors, "schema", f"{where}: an accepted goal is missing goal or evidence")
        elif not row.get("fact_id") and not row.get("source"):
            err(errors, "schema", f"{where}: accepted goal {row.get('goal')!r} cites neither fact_id nor source")
    for row in reach.get("declined_goals") or []:
        if not isinstance(row, dict) or not row.get("goal") or not row.get("reason") or not row.get("source"):
            err(errors, "schema", f"{where}: a declined goal is missing goal, reason or source")


def schema_check_published(doc: Any, errors: list[str]) -> None:
    """Validate against the published Draft 2020-12 schema.

    Opt-in (``--with-jsonschema``) because ``jsonschema`` is not stdlib.  The
    test suite runs it over the committed catalog, which is what stops the
    published schema and the stdlib checks above from drifting apart.
    """
    try:
        import jsonschema  # type: ignore[import-not-found]
    except ImportError:
        err(errors, "schema-published", "jsonschema is not installed, so nothing was compared")
        return
    schema = json.loads(SCHEMA.read_text())
    validator = jsonschema.Draft202012Validator(schema)
    for problem in sorted(validator.iter_errors(doc), key=lambda e: list(e.path)):
        where = ".".join(str(part) for part in problem.path) or "<root>"
        err(errors, "schema-published", f"{where}: {problem.message}")


# --------------------------------------------------------------------------
# Binding the catalog to the code it describes
# --------------------------------------------------------------------------

def rust_consts(text: str) -> dict[str, int]:
    """Every `const NAME: T = <int or alias>;`, aliases resolved one chain deep."""
    raw: dict[str, str] = {}
    for name, value in CONST_DECL.findall(text):
        raw[name] = value.strip()
    resolved: dict[str, int] = {}
    for name in raw:
        value = raw[name]
        for _ in range(8):
            literal = value.replace("_", "")
            if re.fullmatch(r"[0-9]+", literal):
                resolved[name] = int(literal)
                break
            if value in raw:
                value = raw[value].strip()
                continue
            break
    return resolved


def rust_decline_variants(text: str) -> set[str]:
    match = DECLINE_ENUM.search(text)
    if match is None:
        return set()
    return set(VARIANT.findall(match.group(1)))


def overlay_capabilities(root: Path, errors: list[str]) -> set[str]:
    path = root / "artifacts/autogenesis/knowledge-overlay-v1.json"
    try:
        overlay = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        err(errors, "capability", f"cannot read the knowledge overlay: {exc}")
        return set()
    capabilities = {
        entity["id"] for entity in overlay.get("entities", [])
        if isinstance(entity, dict) and entity.get("kind") == "capability"
    }
    for source in overlay.get("sources", []):
        if isinstance(source, dict) and source.get("kind", "").startswith("external"):
            err(errors, "capability",
                f"the knowledge overlay declares an external source {source.get('id')!r} (ADR-0553)")
    return capabilities


def check_bindings(
    doc: dict[str, Any],
    root: Path,
    errors: list[str],
    warnings: list[str],
) -> None:
    capabilities = overlay_capabilities(root, errors)
    sources: dict[str, str] = {}

    seen: set[str] = set()
    for tactic in doc["tactics"]:
        ident = tactic.get("id")
        if not isinstance(ident, str):
            continue
        if ident in seen:
            err(errors, "unique-ids", f"duplicate tactic id {ident!r}")
        seen.add(ident)

        implemented_by = tactic.get("implemented_by") or {}
        rel = implemented_by.get("path")
        source_path = root / rel if isinstance(rel, str) else None
        text = None
        if source_path is None or not source_path.is_file():
            err(errors, "implementation-path", f"{ident}: implemented_by.path {rel!r} does not exist")
        else:
            text = sources.get(rel)
            if text is None:
                text = source_path.read_text(errors="replace")
                sources[rel] = text

        symbol = implemented_by.get("symbol")
        if text is not None and isinstance(symbol, str):
            pattern = rf"\b(?:fn|struct|enum|const|static|type)\s+{re.escape(symbol)}\b"
            if re.search(pattern, text) is None:
                err(
                    errors, "implementation-symbol",
                    f"{ident}: symbol {symbol!r} is not declared in {rel}",
                )

        if text is not None:
            variants = rust_decline_variants(text)
            if not variants:
                err(errors, "decline-reason", f"{ident}: no DeclineReason enum found in {rel}")
            for reason in tactic.get("decline_reasons") or []:
                if reason not in variants:
                    err(
                        errors, "decline-reason",
                        f"{ident}: {reason!r} is not a DeclineReason variant in {rel}"
                        f" (variants: {sorted(variants)})",
                    )
            consts = rust_consts(text)
            for name, value in (tactic.get("budget") or {}).items():
                if name not in consts:
                    err(errors, "budget", f"{ident}: no `const {name}` in {rel}")
                elif consts[name] != value:
                    err(
                        errors, "budget",
                        f"{ident}: budget {name}={value} but {rel} declares {consts[name]}",
                    )

        realizes = tactic.get("realizes")
        if realizes not in capabilities:
            err(
                errors, "capability",
                f"{ident}: realizes {realizes!r} is not a capability entity in the knowledge overlay",
            )


        residual = tactic.get("residual") or {}
        shape_none = residual.get("shape") == "none"
        measure_none = residual.get("measure") == "none"
        if shape_none != measure_none:
            err(
                errors, "residual-measure",
                f"{ident}: residual shape and measure must be \"none\" together"
                f" (shape={residual.get('shape')!r}, measure={residual.get('measure')!r})",
            )


# --------------------------------------------------------------------------
# The census
# --------------------------------------------------------------------------

def precondition_signature(tactic: dict[str, Any]) -> str:
    predicates = (tactic.get("precondition") or {}).get("structural", {}).get("all_of", [])
    canonical = sorted(
        json.dumps(predicate, sort_keys=True, ensure_ascii=False)
        for predicate in predicates
        if isinstance(predicate, dict)
    )
    return json.dumps(canonical, ensure_ascii=False)


def census(doc: dict[str, Any], errors: list[str]) -> dict[str, int]:
    tactics = doc["tactics"]
    shapes = {precondition_signature(tactic) for tactic in tactics}
    accepted = 0
    declined = 0
    for tactic in tactics:
        reach = tactic.get("reach") or {}
        rows_accepted = len(reach.get("accepted_goals") or [])
        rows_declined = len(reach.get("declined_goals") or [])
        accepted += rows_accepted
        declined += rows_declined
        if rows_accepted + rows_declined == 0:
            err(
                errors, "reach-empty",
                f"{tactic.get('id')}: zero reach rows -- a tactic with no measured"
                " accepted or declined goal is a name, not a capability",
            )
    if len(shapes) < 2:
        err(
            errors, "precondition-shapes",
            f"only {len(shapes)} distinct precondition shape(s) across {len(tactics)}"
            " tactics -- a catalog whose entries all match one goal shape is a"
            " dispatch table, not a strategy vocabulary",
        )
    return {
        "tactics": len(tactics),
        "distinct_precondition_shapes": len(shapes),
        "accepted_goals": accepted,
        "declined_goals": declined,
        "realizes_capabilities": len({
            tactic.get("realizes") for tactic in tactics if tactic.get("realizes")
        }),
    }


def validate_document(
    doc: Any,
    root: Path = ROOT,
    with_jsonschema: bool = False,
) -> tuple[list[str], list[str], dict[str, int] | None]:
    errors: list[str] = []
    warnings: list[str] = []
    check_structure(doc, errors)
    if with_jsonschema:
        schema_check_published(doc, errors)
    if errors:
        return errors, warnings, None
    check_bindings(doc, root, errors, warnings)
    counts = census(doc, errors)
    return errors, warnings, counts


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument(
        "--with-jsonschema",
        action="store_true",
        help="additionally validate against the published Draft 2020-12 schema"
             " (requires the non-stdlib jsonschema package)",
    )
    args = parser.parse_args()
    try:
        doc = json.loads(args.path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"TACTIC_CATALOG_ERROR|schema|{args.path}: cannot read JSON: {exc}", file=sys.stderr)
        return 1
    errors, warnings, counts = validate_document(
        doc, args.root, args.with_jsonschema
    )
    for warning in warnings:
        print(f"TACTIC_CATALOG_WARNING|{warning}", file=sys.stderr)
    for error in errors:
        print(f"TACTIC_CATALOG_ERROR|{error}", file=sys.stderr)
    if errors or counts is None:
        return 1
    print(
        "TACTIC_CATALOG|"
        f"tactics={counts['tactics']}|"
        f"distinct_precondition_shapes={counts['distinct_precondition_shapes']}|"
        f"accepted_goals={counts['accepted_goals']}|"
        f"declined_goals={counts['declined_goals']}|"
        f"realizes_capabilities={counts['realizes_capabilities']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
