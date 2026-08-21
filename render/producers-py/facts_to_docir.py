#!/usr/bin/env python3
"""Fact ledger -> Doc-IR: one card document per fact, plus an atlas index.

WHAT THIS IS. The P0-B producer of the render strand (docs/render-2026-08,
04-prototype-plan.md). It reads every `artifacts/facts/*.json` and emits Doc-IR
JSON documents (`artifacts/ontology/docir.schema.json`) that assembly resolves
and the emitters turn into Markdown / LaTeX / HTML. Python is a first-class
producer in this design (03-architecture.md: "JSON as interchange so Python
producers/consumers are first-class"); this script is the proof.

WHAT IT NEVER DOES. It writes no mathematics of its own. Statement text is not
copied into the documents at all: `BlockStatement` has no `text` property by
design, so a card names the fact by `FormalRef` and assembly fetches the prose,
the formal statement and both status axes from the ledger. The only prose this
script authors is the derived-from-data disagreement note, and that sentence
names the two status values it was computed from.

IT IS ALSO A CHECKER, and its exit status depends on what it found:

  1. every input fact is validated against `artifacts/ontology/fact.schema.json`
     (jsonschema if importable, else the vendored subset validator below);
  2. duplicate ids, id/filename disagreement, and dangling `depends_on` edges
     are errors -- a dependency DAG with dangling edges is not a build order,
     and a dangling reference is a build error under the fail-closed law;
  3. THE GREEN-BADGE GUARD: a fact whose `epistemic_status` is `proved`,
     `computed` or `refuted` while NO evidence row is `checked` aborts the run
     before anything is written. There is no styling path from absent evidence
     to an established badge, so there must be no emission path either;
  4. the emitted documents are validated against the Doc-IR schema (via
     `scripts/validate-docir.py` when it exists, else jsonschema/vendored
     directly). If that schema is absent the run FAILS unless
     `--allow-missing-docir-schema` is passed: a checker that silently skips
     its own output check is the inert-gate defect this repository keeps
     re-learning.

Nothing is written when any of 1-3 fires, so `exit_status: 0` in an emitted
document's provenance means these checks ran and found nothing -- not merely
that the process completed.

FAIL-CLOSED CONSEQUENCE WORTH KNOWING. These cards contain no `claim` blocks.
A Doc-IR claim must reference a RUN RECORD carrying an exit status, and a fact
ledger evidence row is not one: it carries `check_status: checked`, which is an
assertion that somebody checked it, plus a command a reader can run. So the
evidence renders as `certificate` blocks with a replay command, and the status
badges come from the resolved ledger record through the `statement` block. To
put claims on these pages, the checkers have to actually run and emit records.

DETERMINISM. Sorted keys, sorted iteration, `ensure_ascii=True` (213 of 324
facts hold non-ASCII mathematics; escaping keeps the emitted files ASCII
without altering one character). No wall clock: `meta.epoch` is the commit time
of the last commit touching the facts directory, or SOURCE_DATE_EPOCH, or an
explicit `--epoch-unix`. Identical inputs give byte-identical outputs.

Usage:
    python3 render/producers-py/facts_to_docir.py [--facts-dir DIR]
        [--out-dir DIR] [--epoch-unix N --epoch-source S] [--pilot ID ...]
        [--allow-missing-docir-schema] [--quiet]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FACTS = ROOT / "artifacts" / "facts"
DEFAULT_OUT = ROOT / "render" / "examples-input" / "facts"
FACT_SCHEMA = ROOT / "artifacts" / "ontology" / "fact.schema.json"
DOCIR_SCHEMA = ROOT / "artifacts" / "ontology" / "docir.schema.json"
VALIDATE_DOCIR = ROOT / "scripts" / "validate-docir.py"

GENERATOR = "render/producers-py/facts_to_docir.py"
COMMAND = "python3 render/producers-py/facts_to_docir.py"
DOC_SCHEMA_VERSION = 1

ID_RE = re.compile(r"^F:[a-z0-9]+(-[a-z0-9]+)*$")
SLUG_RE = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

# --- status vocabularies -----------------------------------------------------
# Mirrors scripts/validate-facts.py. These sets are the ONLY place a status is
# interpreted; nothing downstream re-derives one.
OURS_SETTLED = {"proved", "computed", "refuted"}       # what WE established
EXTERNAL_UNSETTLED = {"open", "conjectured"}           # what mathematics has not

# The ledger's `epistemic_status` and the Doc-IR `EvidenceStatus` badge
# vocabulary are NOT the same set, and the mapping is conservative by
# construction: it never produces a badge stronger than the ledger value.
#   proved      -> proved     kernel-admitted / complete proof
#   computed    -> evidence   a finite computation carries no universal credit,
#                             which is exactly what `evidence` means
#   refuted     -> refuted    a witness against the statement
#   conjectured -> open       believed here, established nowhere here
#   open        -> open
#   axiom       -> evidence   assumed, not established (no such fact today)
#   empirical   -> evidence   (no such fact today)
# `checked` and `advisory` are deliberately UNREACHABLE from a fact: `checked`
# would mean this producer had replayed the evidence, and it replays nothing.
EPISTEMIC_TO_BADGE = {
    "proved": "proved",
    "computed": "evidence",
    "refuted": "refuted",
    "conjectured": "open",
    "open": "open",
    "axiom": "evidence",
    "empirical": "evidence",
}
# Badges that assert the statement was settled here. Unreachable with zero
# `checked` evidence rows -- see badge_for_epistemic and the guard in main().
SETTLED_BADGES = {"proved", "checked", "evidence", "refuted"}

# Ledger evidence kind -> Doc-IR `cert_kind`. The ledger has ten kinds and the
# Doc-IR enum has six, so the ledger kind is ALSO carried verbatim in the
# per-row detail table; see the diary's schema-fit list.
CERT_KIND = {
    "kernel-term": "kernel-admission",
    "unsat-certificate": "unsat-drat",
    "witness-replay": "witness-replay",
    "cube-cover": "cube-cover",
    "cube-tree-cover": "cube-cover",
    "exhaustive-enumeration": "report-run",
    "published-value-replication": "report-run",
    "bound-citation": "report-run",
    "instance-pin": "report-run",
    "claim-ref": "report-run",
}

RENDER_HINT = {
    ".json": "json", ".txt": "text", ".log": "text", ".out": "text",
    ".cnf": "code", ".smt2": "code", ".lean": "code", ".drat": "link",
    ".md": "text", ".csv": "table",
}


# --- vendored minimal JSON Schema validator ---------------------------------
# Used only when `jsonschema` is not importable. Covers the keywords actually
# used by fact.schema.json and docir.schema.json. Deliberately strict: an
# unsupported keyword is REPORTED rather than ignored, because a validator that
# silently skips what it does not understand is the inert-gate defect in
# miniature.
_SUPPORTED = {
    "$schema", "$id", "title", "description", "$defs", "definitions",
    "type", "required", "properties", "additionalProperties", "enum", "const",
    "pattern", "minLength", "maxLength", "minimum", "maximum", "items",
    "propertyNames", "$ref", "oneOf", "anyOf", "allOf", "minItems", "examples",
    "default", "uniqueItems", "format", "$comment",
}
_TYPES = {
    "object": dict, "array": list, "string": str, "boolean": bool,
    "number": (int, float), "integer": int, "null": type(None),
}


def _mini_validate(inst, schema, root, path, errs):
    if not isinstance(schema, dict):
        return
    unsupported = set(schema) - _SUPPORTED
    if unsupported:
        errs.append(f"{path}: vendored validator does not implement {sorted(unsupported)}")
    if "$ref" in schema:
        ref = schema["$ref"]
        if not ref.startswith("#/"):
            errs.append(f"{path}: vendored validator cannot resolve $ref {ref!r}")
            return
        target = root
        for part in ref[2:].split("/"):
            target = target.get(part, {})
        _mini_validate(inst, target, root, path, errs)
        return
    t = schema.get("type")
    if t is not None:
        want = t if isinstance(t, list) else [t]
        ok = False
        for w in want:
            py = _TYPES[w]
            if isinstance(inst, py) and not (w in ("number", "integer") and isinstance(inst, bool)):
                ok = True
        if not ok:
            errs.append(f"{path}: expected type {t}, got {type(inst).__name__}")
            return
    if "const" in schema and inst != schema["const"]:
        errs.append(f"{path}: must equal {schema['const']!r}")
    if "enum" in schema and inst not in schema["enum"]:
        errs.append(f"{path}: {inst!r} not in enum {schema['enum']}")
    if isinstance(inst, str):
        if "pattern" in schema and not re.search(schema["pattern"], inst):
            errs.append(f"{path}: {inst!r} does not match {schema['pattern']!r}")
        if "minLength" in schema and len(inst) < schema["minLength"]:
            errs.append(f"{path}: shorter than minLength {schema['minLength']}")
    if isinstance(inst, (int, float)) and not isinstance(inst, bool):
        if "minimum" in schema and inst < schema["minimum"]:
            errs.append(f"{path}: below minimum {schema['minimum']}")
    if isinstance(inst, dict):
        for key in schema.get("required", []):
            if key not in inst:
                errs.append(f"{path}: missing required property {key!r}")
        props = schema.get("properties", {})
        for key in sorted(inst):
            if key in props:
                _mini_validate(inst[key], props[key], root, f"{path}.{key}", errs)
            elif schema.get("additionalProperties") is False:
                errs.append(f"{path}: additional property {key!r} is not allowed")
            elif isinstance(schema.get("additionalProperties"), dict):
                _mini_validate(inst[key], schema["additionalProperties"], root,
                               f"{path}.{key}", errs)
            if "propertyNames" in schema:
                _mini_validate(key, schema["propertyNames"], root, f"{path}<key>", errs)
    if isinstance(inst, list):
        if "minItems" in schema and len(inst) < schema["minItems"]:
            errs.append(f"{path}: fewer than minItems {schema['minItems']}")
        if isinstance(schema.get("items"), dict):
            for i, v in enumerate(inst):
                _mini_validate(v, schema["items"], root, f"{path}[{i}]", errs)
    for i, sub in enumerate(schema.get("allOf", [])):
        _mini_validate(inst, sub, root, f"{path}(allOf[{i}])", errs)
    for key in ("oneOf", "anyOf"):
        subs = schema.get(key)
        if subs:
            branch_errs = []
            ok = False
            for sub in subs:
                sub_errs: list[str] = []
                _mini_validate(inst, sub, root, path, sub_errs)
                if not sub_errs:
                    ok = True
                    break
                branch_errs.append(sub_errs[0])
            if not ok:
                errs.append(f"{path}: matches no branch of {key} ({branch_errs})")


class SchemaValidator:
    """jsonschema when available, the vendored subset otherwise."""

    def __init__(self, schema: dict):
        self.schema = schema
        try:
            import jsonschema  # noqa: F401

            self.backend = "jsonschema"
        except ImportError:
            self.backend = "vendored"

    def errors(self, instance, where: str) -> list[str]:
        if self.backend == "jsonschema":
            import jsonschema

            v = jsonschema.Draft202012Validator(self.schema)
            return [
                f"{where}: {'/'.join(str(p) for p in e.absolute_path) or '<root>'}: "
                f"{e.message[:400]}"
                for e in sorted(v.iter_errors(instance), key=lambda e: list(e.absolute_path))
            ]
        errs: list[str] = []
        _mini_validate(instance, self.schema, self.schema, where, errs)
        return errs


# --- small helpers -----------------------------------------------------------

def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def slug(fact_id: str) -> str:
    """`F:nat-add-comm` -> `F-nat-add-comm` (the ledger's own filename rule)."""
    return fact_id.replace("F:", "F-", 1)


def doc_slug(fact_id: str) -> str:
    """`F:nat-add-comm` -> `fact-nat-add-comm` (DocMeta.doc_id is lowercase)."""
    return "fact-" + fact_id[2:]


def rel(path: Path) -> str:
    try:
        return str(Path(path).resolve().relative_to(ROOT))
    except ValueError:
        return str(path)


def one_line(text: str, limit: int = 400) -> str:
    """Collapse to a single line for a scalar table cell. Never used on a
    statement of record -- only on already-prose fields such as evidence notes,
    which are shown in full in their own prose block."""
    flat = " ".join(str(text).split())
    return flat if len(flat) <= limit else flat[: limit - 3] + "..."


# --- Doc-IR construction -----------------------------------------------------

def provenance(inputs: list[tuple[str, str]], epoch: dict, exit_status: int = 0) -> dict:
    """Provenance for content THIS script produced.

    `command` is always this producer's command line, never a checker command
    out of the ledger: a Provenance asserts that its command ran and exited with
    the recorded status, and this script runs no checkers. A ledger checker
    command appears only as `Certificate.replay`, which is an invitation to the
    reader rather than a record of a run.

    `exit_status: 0` is honest here because nothing is written unless the fact
    validation, the dangling-edge check and the green-badge guard all pass; the
    status depends on the finding, not on completion.
    """
    return {
        "generator": GENERATOR,
        "command": COMMAND,
        "inputs": [{"path": p, "sha256": h} for p, h in inputs],
        "exit_status": exit_status,
        "epoch": epoch,
    }


def block(bid: str, tag: str, kind: dict, prov: dict | None = None,
          title: str | None = None) -> dict:
    assert SLUG_RE.match(bid), f"block id {bid!r} is not a slug"
    b = {"id": bid, "tag": tag, "kind": kind}
    if title:
        b["title"] = title
    if prov is not None:
        b["provenance"] = prov
    return b


def fact_ref(fact_id: str) -> dict:
    return {"kind": "fact", "id": fact_id}


def columns(*pairs: tuple[str, str]) -> list[dict]:
    return [{"key": k, "header": h} for k, h in pairs]


def table_kind(caption: str, cols: list[dict], rows: list[list], source: dict) -> dict:
    for r in rows:
        assert len(r) == len(cols), f"row width {len(r)} != {len(cols)} columns"
    return {"type": "table", "caption": {"text": caption}, "columns": cols,
            "rows": rows, "source": source}


def prose_kind(text: str, heading_level: int | None = None) -> dict:
    k = {"type": "prose", "text": text}
    if heading_level:
        k["heading_level"] = heading_level
    return k


# --- status logic (mirrors validate-facts.py; never infers, never upgrades) --

def badge_for_epistemic(status: str, checked: int) -> str:
    """Ledger `epistemic_status` -> Doc-IR `EvidenceStatus`.

    Two independent guards keep an unsupported fact off a settled badge: this
    downgrade, and the abort in main(). Belt and braces on purpose -- this is
    the one function whose output an emitter is allowed to paint green.
    """
    badge = EPISTEMIC_TO_BADGE.get(status, "open")
    if badge in SETTLED_BADGES and checked == 0:
        return "open"
    return badge


def external_label(value: str | None) -> tuple[str, str]:
    """(label, basis) for `external_status`.

    ABSENT and `unknown` are different and stay different: the schema says omit
    the field when nobody has looked, while `unknown` means nobody has looked
    AND we checked. Collapsing them would erase a measurement.
    """
    if value is None:
        return ("unclassified", "field absent: nobody has looked "
                                "(distinct from `unknown`, which means we checked)")
    return (value, "copied from the ledger's external_status")


def disagreement(status: str, external: str | None) -> dict | None:
    """The two axes disagreeing, in either direction. Mirrors validate-facts.py.

    NOVEL (`novel` there): established here, unsettled in the literature -- the
    output this project exists to produce, which the validator prints rather
    than fails. BACKLOG (`backlog` there): open here, proved in the literature
    -- an import target, and the self-extension loop must not treat it as a
    problem to solve.
    """
    if status in OURS_SETTLED and external in EXTERNAL_UNSETTLED:
        return {"kind": "novel", "summary":
                f"Disagreement in our favour: this ledger has established the statement "
                f"(epistemic_status: {status}) while the literature has not "
                f"(external_status: {external}). Both values are copied from the fact "
                f"record; nothing here infers either."}
    if status == "open" and external == "proved":
        return {"kind": "import-backlog", "summary":
                "Import backlog: open in this ledger (epistemic_status: open) and settled "
                "in the literature (external_status: proved). That is a target for import, "
                "not a result of this project."}
    return None


# --- artifact resolution -----------------------------------------------------

def resolve_artifact(art: str) -> tuple[dict, str]:
    """Map an evidence `artifact` string to an (ArtifactRef, state).

    The ledger uses this field three ways (measured over 104 rows): a repo-
    relative file path (96), a bare `sha256:...` content digest with no file
    (6), and a directory (2). None of them is silently treated as a present,
    hashable file.
    """
    if art.startswith("sha256:") and re.fullmatch(r"[0-9a-f]{64}", art[7:]):
        return ({"path": art, "sha256": art[7:],
                 "label": "content digest; no file of this name in the tree"},
                "content-hash-only")
    p = ROOT / art
    if p.is_file():
        return ({"path": art, "sha256": sha256_file(p), "bytes": p.stat().st_size},
                "present")
    if p.is_dir():
        return ({"path": art, "label": "directory, not a single artifact"}, "directory")
    return ({"path": art, "label": "not present in the working tree"}, "missing")


# --- card document -----------------------------------------------------------

def build_card(fact: dict, path: Path, digest: str, dependents: list[str],
               facts: dict[str, dict], epoch: dict) -> tuple[dict, list[str]]:
    fid = fact["id"]
    src = rel(path)
    prov = provenance([(src, digest)], epoch)
    warnings: list[str] = []
    checked = sum(1 for e in fact["evidence"] if e.get("check_status") == "checked")
    badge = badge_for_epistemic(fact["epistemic_status"], checked)
    ext_label, ext_basis = external_label(fact.get("external_status"))
    dis = disagreement(fact["epistemic_status"], fact.get("external_status"))

    blocks: list[dict] = []

    # 1. The statement of record, by checked reference. No text is inlined:
    #    assembly resolves the ledger entry and renders the projection named in
    #    `show`. That is the whole point of the block kind.
    blocks.append(block(
        "statement", "essential",
        {"type": "statement", "ref": fact_ref(fid),
         "show": ["title", "prose", "formal", "status", "proof_route",
                  "axiom_footprint", "depends_on", "evidence_count"]},
        prov, title=fact["title"],
    ))

    # 2. Both status axes as data. Rendered from the ledger values; the badge
    #    column is the conservative mapping in badge_for_epistemic.
    blocks.append(block(
        "status-axes", "essential",
        table_kind(
            "Status, both axes",
            columns(("axis", "axis"), ("ledger_value", "ledger value"),
                    ("badge", "rendered badge"), ("basis", "basis")),
            [
                ["epistemic (what this ledger established)", fact["epistemic_status"],
                 badge, f"{checked} of {len(fact['evidence'])} evidence row(s) checked"],
                ["external (what mathematics knows)", ext_label,
                 ext_label, ext_basis],
            ],
            prov),
        prov, title="Status",
    ))

    if dis:
        blocks.append(block(f"disagreement-{dis['kind']}", "essential",
                            prose_kind(dis["summary"]), prov,
                            title=("Established here, not in the literature"
                                   if dis["kind"] == "novel" else "Import backlog")))

    # 3. Route and footprint, never shown apart: `axiom_footprint: []` is the
    #    project's strongest claim and is only meaningful within a route.
    if fact.get("proof_route") is not None or "axiom_footprint" in fact:
        fp = fact.get("axiom_footprint")
        if fp is None:
            fp_text = "absent -- not a claim of axiom-freedom"
        elif fp == []:
            fp_text = "[] -- axiom-free; only kernel-lean can deliver this"
        else:
            fp_text = "; ".join(fp)
        blocks.append(block(
            "trust-base", "essential",
            table_kind("Trust base", columns(("field", "field"), ("value", "value")),
                       [["proof_route", fact.get("proof_route") or "(none recorded)"],
                        ["axiom_footprint", fp_text]],
                       prov),
            prov, title="Trust base",
        ))

    # 4. Evidence. A `certificate` block per row that carries a replay command,
    #    plus a detail table holding every ledger field the certificate shape
    #    has no home for, plus the row's own prose notes, plus an `include` for
    #    an artifact that is actually in the tree.
    for i, e in enumerate(fact["evidence"]):
        art_ref, art_state = (None, None)
        if e.get("artifact"):
            art_ref, art_state = resolve_artifact(e["artifact"])
            if art_state == "missing":
                warnings.append(f"{fid}: evidence {e['id']} names artifact "
                                f"{e['artifact']}, which is not in the working tree")
        cmd = e.get("checker_command")
        if cmd:
            replay = {"line": cmd, "cwd": ".", "expected_exit_status": 0}
            if e.get("checker_seconds"):
                replay["expected_seconds"] = e["checker_seconds"]
            cert = {
                "type": "certificate",
                "cert_kind": CERT_KIND.get(e["kind"], "report-run"),
                "summary": {"text": e["supports"]},
                "artifact_refs": [art_ref] if art_ref else [],
                "replay": replay,
            }
            blocks.append(block(f"evidence-{i:03d}", "detail", cert, prov,
                                title=f"Evidence: {e['id']}"))
        else:
            warnings.append(f"{fid}: evidence {e['id']} carries no checker_command, so it "
                            f"renders with no replay route and cannot be a certificate")

        rows = [["evidence id", e["id"]],
                ["ledger kind", e["kind"]],
                ["cert_kind", CERT_KIND.get(e["kind"], "report-run")],
                ["check_status", e["check_status"]],
                ["independent checkers", ", ".join(e.get("checkers", [])) or "(none named)"],
                ["supports", one_line(e["supports"], 600)]]
        if art_ref:
            rows.append(["artifact", art_ref["path"]])
            rows.append(["artifact state", art_state])
            rows.append(["artifact sha256", art_ref.get("sha256") or "(not hashed)"])
        if not cmd:
            rows.append(["replay command", "(absent from the ledger row)"])
        for extra in ("measurement", "checker_operation", "checker_seconds"):
            if extra in e:
                rows.append([extra, one_line(e[extra], 600)])
        blocks.append(block(
            f"evidence-{i:03d}-record", "detail",
            table_kind(f"Evidence row {e['id']} as recorded in the ledger",
                       columns(("field", "field"), ("value", "value")), rows, prov),
            prov,
        ))
        if e.get("notes"):
            blocks.append(block(f"evidence-{i:03d}-notes", "archive",
                                prose_kind(e["notes"]), prov))
        if art_state == "present":
            ext = Path(art_ref["path"]).suffix
            blocks.append(block(
                f"evidence-{i:03d}-artifact", "archive",
                {"type": "include", "path": art_ref["path"],
                 "render_hint": RENDER_HINT.get(ext, "link"),
                 "sha256": art_ref["sha256"], "max_bytes": 65536,
                 "caption": {"text": f"Artifact for evidence {e['id']}"}},
                prov))

    # 5. Local dependency neighbourhood. `href` on a dep-graph node is the only
    #    place the schema carries a link (a table Cell is a scalar by design),
    #    so this is how a card links to its neighbours' cards.
    neighbours = sorted(set(fact["depends_on"]) | set(dependents) | {fid})
    if len(neighbours) > 1:
        blocks.append(block(
            "dependency-graph", "detail",
            {"type": "figure",
             "caption": {"text": "Immediate dependencies and dependents of this fact"},
             "alt": f"Dependency graph around {fid}: {len(fact['depends_on'])} "
                    f"dependencies, {len(dependents)} dependents",
             "spec": dep_graph_spec(neighbours, facts, focus=fid)},
            prov, title="Dependency neighbourhood",
        ))

    for bid, cap, ids in (("depends-on", "Depends on", sorted(fact["depends_on"])),
                          ("depended-on-by", "Depended on by", sorted(dependents))):
        if ids:
            blocks.append(block(
                bid, "detail",
                table_kind(cap, columns(("fact", "fact"), ("title", "title"),
                                        ("epistemic", "epistemic status"),
                                        ("card", "card")),
                           [[d, facts[d]["title"], facts[d]["epistemic_status"],
                             f"cards/{slug(d)}.doc.json"] for d in ids],
                           prov),
                prov, title=cap,
            ))

    # 6. The fact's own provenance and prior art, verbatim.
    fprov = fact["provenance"]
    blocks.append(block(
        "fact-provenance", "detail",
        table_kind("Provenance recorded in the ledger",
                   columns(("field", "field"), ("value", "value")),
                   [[k, one_line(fprov[k], 800)] for k in sorted(fprov) if k != "prior_art"],
                   prov),
        prov, title="Provenance",
    ))
    if fprov.get("prior_art"):
        keys: list[str] = []
        for pa in fprov["prior_art"]:
            for k in sorted(pa):
                if k not in keys:
                    keys.append(k)
        blocks.append(block(
            "prior-art", "detail",
            table_kind("Prior art recorded in the ledger",
                       columns(*[(k, k) for k in keys]),
                       [[one_line(pa[k], 600) if k in pa else None for k in keys]
                        for pa in fprov["prior_art"]],
                       prov),
            prov, title="Prior art",
        ))

    if fact.get("concept_refs"):
        blocks.append(block(
            "concept-refs", "archive",
            table_kind("Concept references (gloss and provenance only, never substance)",
                       columns(("graph", "graph"), ("ref", "ref"),
                               ("relation", "relation"), ("resolved", "resolved")),
                       [[c.get("graph"), c.get("ref"), c.get("relation"), c.get("resolved")]
                        for c in fact["concept_refs"]],
                       prov),
            prov,
        ))

    if fact.get("supersedes"):
        blocks.append(block(
            "supersedes", "detail",
            table_kind("Supersedes", columns(("fact", "fact"), ("card", "card")),
                       [[s, f"cards/{slug(s)}.doc.json"] for s in sorted(fact["supersedes"])],
                       prov),
            prov,
        ))

    if fact.get("notes"):
        blocks.append(block("ledger-notes", "detail", prose_kind(fact["notes"]), prov,
                            title="Notes from the ledger"))

    doc = {
        "schema_version": DOC_SCHEMA_VERSION,
        "meta": {
            "doc_id": doc_slug(fid),
            "genre": "result",
            "title": fact["title"],
            "subtitle": f"Fact card for {fid}",
            "epoch": epoch,
            "options": {"markdown": {"badge_style": "text"}},
        },
        "blocks": blocks,
        "provenance": prov,
    }
    return doc, warnings


# --- graph, atlas and pilot documents ---------------------------------------

def short_label(fact_id: str) -> str:
    """The fact id without its `F:` prefix and without a trailing content hash.

    `F:ml430-nat-fib-add-two-b86e0c82` -> `ml430-nat-fib-add-two`. The hash is
    dropped only when it is exactly eight hex digits, so an id that genuinely
    ends in a short hex-looking word keeps it.
    """
    body = fact_id[2:] if fact_id.startswith("F:") else fact_id
    head, _, tail = body.rpartition("-")
    if head and len(tail) == 8 and all(c in "0123456789abcdef" for c in tail):
        return head
    return body


def dep_graph_spec(ids: list[str], facts: dict[str, dict],
                   focus: str | None = None) -> dict:
    """FigureDepGraph over `depends_on`.

    Edge direction is dependent -> dependency (`from` needs `to`), matching the
    field it is built from. Restricted to `ids`: an edge with an end outside the
    set is dropped, and the caller counts what it kept.
    """
    inside = set(ids)
    nodes = []
    for i in sorted(ids):
        f = facts[i]
        checked = sum(1 for e in f["evidence"] if e.get("check_status") == "checked")
        # THE BOX LABEL IS THE SHORT ID, NOT THE TITLE, and the title is the
        # tooltip. Measured 2026-08-21 on the rendered atlas: a node box holds
        # about fifteen characters on each of two lines, and nine facts of the
        # Fibonacci component are titled `Mathlib v4.30 source proposition
        # Nat.fib_...`, so every one of them drew as `Mathlib v4.30 source~`.
        # Nine identical boxes is a picture of nothing. The short id
        # (`ml430-nat-fib-add-two`) is distinguishing by construction, fits a
        # box, and the full title is one hover away.
        node = {"id": i, "label": short_label(i), "tooltip": f["title"],
                "status": badge_for_epistemic(f["epistemic_status"], checked),
                "href": f"cards/{slug(i)}.doc.json",
                "group": f.get("proof_route") or "unproved"}
        if focus == i:
            node["group"] = "focus"
        nodes.append(node)
    edges = [{"from": i, "to": d, "label": "depends_on"}
             for i in sorted(ids) for d in sorted(facts[i]["depends_on"]) if d in inside]
    return {"figure_type": "dep-graph", "nodes": nodes, "edges": edges, "rankdir": "TB"}


def count_edges(ids: list[str], facts: dict[str, dict]) -> int:
    inside = set(ids)
    return sum(1 for i in ids for d in facts[i]["depends_on"] if d in inside)


def index_table(ids: list[str], facts: dict[str, dict], prov: dict) -> dict:
    cols = columns(("fact", "fact"), ("title", "title"), ("language", "language"),
                   ("fragment", "fragment"), ("route", "proof_route"),
                   ("epistemic", "epistemic"), ("external", "external"),
                   ("badge", "badge"), ("flag", "flag"),
                   ("evidence", "evidence"), ("checked", "checked"),
                   ("card", "card"))
    rows = []
    for i in sorted(ids):
        f = facts[i]
        checked = sum(1 for e in f["evidence"] if e.get("check_status") == "checked")
        dis = disagreement(f["epistemic_status"], f.get("external_status"))
        rows.append([
            i, f["title"], f["formal"]["language"], f["formal"]["fragment"],
            f.get("proof_route") or "-", f["epistemic_status"],
            external_label(f.get("external_status"))[0],
            badge_for_epistemic(f["epistemic_status"], checked),
            dis["kind"] if dis else "-",
            len(f["evidence"]), checked, f"cards/{slug(i)}.doc.json",
        ])
    return table_kind("Fact index", cols, rows, prov)


def spread_table(ids: list[str], facts: dict[str, dict], prov: dict) -> dict:
    axes: list[tuple[str, dict[str, int]]] = [
        ("epistemic_status", {}), ("external_status", {}), ("proof_route", {}),
        ("formal.language", {}),
    ]
    for i in ids:
        f = facts[i]
        axes[0][1][f["epistemic_status"]] = axes[0][1].get(f["epistemic_status"], 0) + 1
        k = f.get("external_status") or "(absent)"
        axes[1][1][k] = axes[1][1].get(k, 0) + 1
        r = f.get("proof_route") or "(none)"
        axes[2][1][r] = axes[2][1].get(r, 0) + 1
        lang = f["formal"]["language"]
        axes[3][1][lang] = axes[3][1].get(lang, 0) + 1
    rows = [[axis, k, d[k]] for axis, d in axes for k in sorted(d)]
    return table_kind("Ledger spread over the documented facts",
                      columns(("axis", "axis"), ("value", "value"), ("facts", "facts")),
                      rows, prov)


# One picture of the WHOLE ledger is not a picture. Measured 2026-08-21: the
# layered layout over all 324 facts is 32,936 x 674 px, because 173 of them have
# no `depends_on` edge in either direction and land in a single row. Scaled into
# a 68rem column that row is about two pixels tall -- present, legible to
# nobody. So above this many nodes the atlas ships ONE GRAPH PER CONNECTED
# COMPONENT plus the full index table, and says in prose why. The threshold is
# where a layer stops fitting a printed page at a readable node size, not a
# round number: 40 nodes * ~110 px is already 4,400 px, i.e. a 4x downscale.
GRAPH_ONE_PICTURE_MAX = 40
# A component this size or larger is shown open; the rest fold. Both are
# rendered -- `detail` folds, it does not drop (that is `archive`).
GRAPH_ESSENTIAL_MIN = 5


def graph_blocks(ids: list[str], facts: dict[str, dict], edges: int,
                 prov: dict) -> list[dict]:
    """The dependency figure(s) for an atlas-style document.

    Small documents get the one graph they deserve. Large ones get one graph per
    connected component, in descending size order, and a note stating the
    measurement that forced the split -- a reader who cannot see why a picture
    is missing has to take the renderer's word for it.
    """
    if len(ids) <= GRAPH_ONE_PICTURE_MAX:
        return [block(
            "dep-graph", "essential",
            {"type": "figure",
             "caption": {"text": f"`depends_on` over {len(ids)} facts, {edges} edges. "
                                 f"An edge runs from the dependent fact to the fact it "
                                 f"rests on. Node status is the conservative mapping of "
                                 f"the ledger's epistemic_status."},
             "alt": f"Dependency graph of {len(ids)} facts with {edges} edges",
             "spec": dep_graph_spec(ids, facts)},
            prov, title="Dependency graph",
        )]

    comps = components(ids, facts)
    nontrivial = sorted((c for c in comps if len(c) > 1),
                        key=lambda c: (-len(c), c[0]))
    isolated = sorted(c[0] for c in comps if len(c) == 1)
    out = [block(
        "dep-graph-note", "essential",
        prose_kind(
            f"The `depends_on` relation over these {len(ids)} facts has {edges} "
            f"edges and falls into {len(comps)} connected components: "
            f"{len(nontrivial)} with more than one fact ({sum(len(c) for c in nontrivial)} "
            f"facts between them, the largest holding {len(nontrivial[0])}), and "
            f"{len(isolated)} single facts that nothing in the ledger depends on "
            f"and that depend on nothing in it.\n\n"
            f"One drawing of all {len(ids)} would be {len(ids)} nodes wide and four "
            f"layers deep -- a strip some thirty thousand pixels across, which at "
            f"page width is a smear. So each component is drawn on its own below, "
            f"largest first, and the {len(isolated)} unconnected facts appear in the "
            f"index table rather than as a row of dots. The index is the complete "
            f"list either way: every fact is in it."),
        prov, title="Dependency structure",
    )]
    for n, comp in enumerate(nontrivial, start=1):
        ce = count_edges(comp, facts)
        tag = "essential" if len(comp) >= GRAPH_ESSENTIAL_MIN else "detail"
        out.append(block(
            f"dep-graph-c{n:02d}", tag,
            {"type": "figure",
             "caption": {"text": f"Component {n} of {len(nontrivial)}: {len(comp)} facts, "
                                 f"{ce} edges. An edge runs from the dependent fact to "
                                 f"the fact it rests on."},
             "alt": f"Dependency graph of {len(comp)} facts with {ce} edges",
             "spec": dep_graph_spec(comp, facts)},
            prov, title=f"Component {n} ({len(comp)} facts)",
        ))
    return out


def build_atlas(ids: list[str], facts: dict[str, dict], digests: dict[str, str],
                epoch: dict, doc_id: str, title: str, subtitle: str,
                intro: str) -> dict:
    inputs = [(f"artifacts/facts/{slug(i)}.json", digests[i]) for i in sorted(ids)]
    prov = provenance(inputs, epoch)
    edges = count_edges(ids, facts)
    novel, backlog = [], []
    for i in sorted(ids):
        d = disagreement(facts[i]["epistemic_status"], facts[i].get("external_status"))
        if d and d["kind"] == "novel":
            novel.append(i)
        elif d and d["kind"] == "import-backlog":
            backlog.append(i)

    blocks = [block("intro", "essential", prose_kind(intro), prov, title=title)]
    if novel:
        blocks.append(block(
            "novel", "essential",
            table_kind("Established here, not settled in the literature",
                       columns(("fact", "fact"), ("title", "title"),
                               ("epistemic", "epistemic"), ("external", "external"),
                               ("card", "card")),
                       [[i, facts[i]["title"], facts[i]["epistemic_status"],
                         external_label(facts[i].get("external_status"))[0],
                         f"cards/{slug(i)}.doc.json"] for i in novel],
                       prov),
            prov, title="Disagreements in our favour",
        ))
    blocks.extend(graph_blocks(ids, facts, edges, prov))
    blocks.append(block("spread", "essential", spread_table(ids, facts, prov), prov,
                        title="Spread"))
    blocks.append(block("index", "essential", index_table(ids, facts, prov), prov,
                        title="Index"))
    if backlog:
        blocks.append(block(
            "import-backlog", "detail",
            table_kind("Settled in the literature, open here (import backlog)",
                       columns(("fact", "fact"), ("title", "title"), ("card", "card")),
                       [[i, facts[i]["title"], f"cards/{slug(i)}.doc.json"]
                        for i in backlog],
                       prov),
            prov, title="Import backlog",
        ))
    return {
        "schema_version": DOC_SCHEMA_VERSION,
        "meta": {"doc_id": doc_id, "genre": "result", "title": title,
                 "subtitle": subtitle, "epoch": epoch,
                 "options": {"markdown": {"badge_style": "text"}}},
        "blocks": blocks,
        "provenance": prov,
    }


# --- pilot subgraph ----------------------------------------------------------

def components(ids: list[str], facts: dict[str, dict]) -> list[list[str]]:
    parent = {i: i for i in ids}

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in ids:
        for d in facts[i]["depends_on"]:
            ra, rb = find(i), find(d)
            if ra != rb:
                parent[ra] = rb
    out: dict[str, list[str]] = {}
    for i in ids:
        out.setdefault(find(i), []).append(i)
    return [sorted(v) for v in out.values()]


# The pilot: the only connected component of the whole ledger in the 8-20 band
# whose facts do NOT all share one epistemic status. Measured over 324 facts and
# 135 edges: 39 components of size >= 2, of which exactly two are status-mixed
# and only this one is in band. It is also the strand's own subject -- one
# kernel-lean, axiom-free root with eight open descendants the literature has
# proved -- so it renders the frontier rather than finished work.
PILOT_SEED = "F:ml430-nat-fib-add-two-b86e0c82"
# Secondary, dense, uniformly green: the ancestor closure of Euclid's lemma, the
# infinitude of primes and the power law inside the ledger's largest component.
# Kept because the primary pilot is a tree and a layout engine needs something
# with real branching to be worth anything.
PILOT2_ROOTS = ["F:nat-euclid-lemma", "F:nat-exists-prime-gt", "F:nat-pow-add"]


def ancestor_closure(roots: list[str], facts: dict[str, dict]) -> list[str]:
    seen: set[str] = set()
    stack = [r for r in roots]
    while stack:
        i = stack.pop()
        if i in seen or i not in facts:
            continue
        seen.add(i)
        stack.extend(facts[i]["depends_on"])
    return sorted(seen)


# --- epoch -------------------------------------------------------------------

def resolve_epoch(args, facts_dir: Path) -> tuple[dict | None, str | None]:
    """Epoch as INPUT, never observed. Precedence: explicit flag, then
    SOURCE_DATE_EPOCH, then the commit that last touched the facts directory.

    The last of these is what keeps regeneration stable: the ledger's own last
    commit does not move when an unrelated lane commits, so re-running this
    producer on an unchanged ledger reproduces the bytes.
    """
    if args.epoch_unix is not None:
        e = {"unix": args.epoch_unix, "source": args.epoch_source}
        if args.epoch_commit:
            e["commit"] = args.epoch_commit
        return e, None
    sde = os.environ.get("SOURCE_DATE_EPOCH")
    if sde and sde.isdigit():
        return {"unix": int(sde), "source": "source-date-epoch"}, None
    try:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "log", "-1", "--format=%ct %H", "--", str(facts_dir)],
            capture_output=True, text=True, check=False)
        parts = out.stdout.split()
        if out.returncode == 0 and len(parts) == 2 and parts[0].isdigit():
            return {"unix": int(parts[0]), "source": "commit", "commit": parts[1]}, None
    except OSError:
        pass
    return None, ("no epoch: SOURCE_DATE_EPOCH is unset and git could not date "
                  f"{rel(facts_dir)}. Pass --epoch-unix N [--epoch-source fixed]; "
                  "the renderer never reads the clock.")


# --- output ------------------------------------------------------------------

def write_json(path: Path, doc: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(doc, sort_keys=True, indent=2, ensure_ascii=True) + "\n"
    path.write_text(text, encoding="ascii")


def validate_outputs(docs: list[tuple[Path, dict]], allow_missing: bool,
                     quiet: bool) -> list[str]:
    if not DOCIR_SCHEMA.is_file():
        msg = (f"{rel(DOCIR_SCHEMA)} does not exist, so the emitted documents were NOT "
               f"checked against the Doc-IR schema")
        if allow_missing:
            print(f"  NOTICE {msg} (--allow-missing-docir-schema)")
            return []
        return [msg + " -- pass --allow-missing-docir-schema to accept that explicitly"]
    if VALIDATE_DOCIR.is_file():
        paths = [str(p) for p, _ in docs]
        proc = subprocess.run([sys.executable, str(VALIDATE_DOCIR), *paths],
                              capture_output=True, text=True)
        # CORE's validator also validates run records (`--kind run-record`), so
        # it may require the kind explicitly. An argparse usage error is exit 2;
        # retry once with the document kind rather than reporting a checker
        # interface mismatch as a document defect.
        if proc.returncode == 2 and "usage" in (proc.stderr or "").lower():
            proc = subprocess.run(
                [sys.executable, str(VALIDATE_DOCIR), "--kind", "document", *paths],
                capture_output=True, text=True)
        if not quiet:
            for line in (proc.stdout or "").splitlines()[-10:]:
                print(f"  validate-docir: {line}")
        if proc.returncode != 0:
            tail = (proc.stderr or proc.stdout).strip().splitlines()
            return [f"scripts/validate-docir.py exited {proc.returncode}"] + \
                   [f"  {ln}" for ln in tail[:20]]
        return []
    v = SchemaValidator(json.loads(DOCIR_SCHEMA.read_text()))
    errors: list[str] = []
    for p, doc in docs:
        errors.extend(v.errors(doc, rel(p))[:5])
        if len(errors) > 40:
            errors.append("... further output errors suppressed")
            break
    if not quiet and not errors:
        print(f"  {len(docs)} emitted document(s) validate against {rel(DOCIR_SCHEMA)} "
              f"({v.backend} backend)")
    return errors


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--facts-dir", default=str(DEFAULT_FACTS))
    ap.add_argument("--out-dir", default=str(DEFAULT_OUT))
    ap.add_argument("--epoch-unix", type=int, default=None)
    ap.add_argument("--epoch-source", default="fixed",
                    choices=["commit", "source-date-epoch", "fixed"])
    ap.add_argument("--epoch-commit", default=None)
    ap.add_argument("--allow-missing-docir-schema", action="store_true")
    ap.add_argument("--pilot", nargs="*", default=None,
                    help="explicit pilot fact ids (default: the measured mixed component)")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    facts_dir = Path(args.facts_dir)
    out_dir = Path(args.out_dir)
    if not FACT_SCHEMA.is_file():
        print(f"facts_to_docir: missing {rel(FACT_SCHEMA)}", file=sys.stderr)
        return 2
    if not facts_dir.is_dir():
        print(f"facts_to_docir: missing facts dir {facts_dir}", file=sys.stderr)
        return 2

    fv = SchemaValidator(json.loads(FACT_SCHEMA.read_text()))
    errors: list[str] = []
    warnings: list[str] = []
    skipped: list[str] = []

    facts: dict[str, dict] = {}
    digests: dict[str, str] = {}
    src_path: dict[str, Path] = {}
    paths = sorted(facts_dir.glob("*.json"))
    for p in paths:
        try:
            fact = json.loads(p.read_text())
        except json.JSONDecodeError as exc:
            errors.append(f"{p.name}: not valid JSON: {exc}")
            skipped.append(f"{p.name} (unparseable)")
            continue
        errs = fv.errors(fact, p.name)
        if errs:
            errors.extend(errs[:5])
            skipped.append(f"{p.name} (fails fact.schema.json)")
            continue
        fid = fact["id"]
        if not ID_RE.match(fid):
            errors.append(f"{p.name}: id {fid!r} does not match the fact id pattern")
            skipped.append(f"{p.name} (bad id)")
            continue
        if p.name != slug(fid) + ".json":
            errors.append(f"{fid}: lives in {p.name} but its id implies {slug(fid)}.json")
        if fid in facts:
            errors.append(f"{fid}: duplicate id, also in {src_path[fid].name}")
            skipped.append(f"{p.name} (duplicate id)")
            continue
        facts[fid] = fact
        digests[fid] = sha256_file(p)
        src_path[fid] = p

    # A build order with dangling edges is not one.
    edges = 0
    for fid in sorted(facts):
        for d in facts[fid]["depends_on"]:
            edges += 1
            if d not in facts:
                errors.append(f"{fid}: depends_on {d} does not exist in {rel(facts_dir)} "
                              f"-- a dependency DAG with dangling edges is not a build "
                              f"order, and a dangling reference is a build error")

    # THE GREEN-BADGE GUARD, plus the ledger's own contradiction rule.
    for fid in sorted(facts):
        f = facts[fid]
        checked = sum(1 for e in f["evidence"] if e.get("check_status") == "checked")
        if f["epistemic_status"] in OURS_SETTLED and checked == 0:
            errors.append(
                f"{fid}: epistemic_status {f['epistemic_status']!r} with no `checked` "
                f"evidence row. Rendering that as established would put a settled badge "
                f"on a fact nothing established, so this fact is not emitted.")
        if f["epistemic_status"] == "open" and f["evidence"]:
            errors.append(f"{fid}: status `open` carrying {len(f['evidence'])} evidence "
                          f"row(s) -- an open fact with evidence is a contradiction")

    if errors:
        print(f"facts_to_docir: {len(facts)} facts read, {len(errors)} error(s); "
              f"NOTHING WAS WRITTEN", file=sys.stderr)
        for e in errors:
            print(f"  ERROR {e}", file=sys.stderr)
        for s in skipped:
            print(f"  SKIPPED {s}", file=sys.stderr)
        return 1

    epoch, epoch_err = resolve_epoch(args, facts_dir)
    if epoch is None:
        print(f"facts_to_docir: {epoch_err}", file=sys.stderr)
        return 1

    dependents: dict[str, list[str]] = {i: [] for i in facts}
    for i in sorted(facts):
        for d in facts[i]["depends_on"]:
            dependents[d].append(i)

    emitted: list[tuple[Path, dict]] = []
    for fid in sorted(facts):
        doc, warn = build_card(facts[fid], src_path[fid], digests[fid],
                               dependents[fid], facts, epoch)
        warnings.extend(warn)
        emitted.append((out_dir / "cards" / f"{slug(fid)}.doc.json", doc))

    all_ids = sorted(facts)
    emitted.append((out_dir / "facts-atlas.doc.json", build_atlas(
        all_ids, facts, digests, epoch, "fact-atlas",
        "Fact atlas: the whole ledger",
        f"{len(all_ids)} facts, {edges} depends_on edges",
        f"Every fact in `artifacts/facts/` ({len(all_ids)} facts, {edges} `depends_on` "
        f"edges), both of its status axes, and the dependency graph they form. Every "
        f"status here is copied from the ledger; nothing infers or upgrades one, and the "
        f"badge column is a conservative mapping that can only weaken a ledger value. "
        f"Facts established here but not settled in the literature are listed first: that "
        f"disagreement is the output this project exists to produce.")))

    if args.pilot:
        unknown = sorted(set(args.pilot) - set(facts))
        if unknown:
            print(f"facts_to_docir: --pilot names unknown fact(s): {unknown}",
                  file=sys.stderr)
            return 1
        pilot_ids = sorted(set(args.pilot))
    else:
        pilot_ids = next((c for c in components(all_ids, facts) if PILOT_SEED in c), [])
    if pilot_ids:
        pe = count_edges(pilot_ids, facts)
        emitted.append((out_dir / "facts-pilot.doc.json", build_atlas(
            pilot_ids, facts, digests, epoch, "fact-pilot",
            "Pilot: the Fibonacci frontier",
            f"{len(pilot_ids)} facts, {pe} depends_on edges",
            f"A connected subgraph of the ledger ({len(pilot_ids)} facts, {pe} "
            f"`depends_on` edges) chosen for status mixture: measured over the whole "
            f"ledger it is the only connected component in the 8-20 band that does not "
            f"carry a single epistemic status throughout. One fact is proved here on the "
            f"`kernel-lean` route with an empty axiom footprint; the rest are open here "
            f"and proved in the literature, so this page shows the self-extension "
            f"frontier rather than finished work.")))
    pilot2_ids = ancestor_closure(PILOT2_ROOTS, facts) if not args.pilot else []
    if pilot2_ids:
        p2e = count_edges(pilot2_ids, facts)
        emitted.append((out_dir / "facts-pilot-arith.doc.json", build_atlas(
            pilot2_ids, facts, digests, epoch, "fact-pilot-arith",
            "Pilot, dense alternative: Euclid's lemma and the infinitude of primes",
            f"{len(pilot2_ids)} facts, {p2e} depends_on edges",
            f"The `depends_on` ancestor closure of {', '.join(PILOT2_ROOTS)} inside the "
            f"ledger's largest component ({len(pilot2_ids)} facts, {p2e} edges). Every "
            f"fact here is proved on the `kernel-lean` route with an empty axiom "
            f"footprint, so it exercises graph layout and branching rather than badge "
            f"variety -- the complement of the primary pilot.")))

    for path, doc in emitted:
        write_json(path, doc)

    out_errors = validate_outputs(emitted, args.allow_missing_docir_schema, args.quiet)

    cards = sum(1 for p, _ in emitted if p.parent.name == "cards")
    ev_rows = sum(len(f["evidence"]) for f in facts.values())
    manifest = {
        "generator": GENERATOR,
        "docir_schema_version": DOC_SCHEMA_VERSION,
        "counts": {
            "facts_read": len(facts),
            "cards_emitted": cards,
            "documents_emitted": len(emitted),
            "depends_on_edges": edges,
            "evidence_rows": ev_rows,
            "skipped": len(skipped),
            "warnings": len(warnings),
        },
        # Relative to the output directory, not to the repository root: the
        # manifest must not change when the same documents are emitted
        # somewhere else (an A/B build, a temp dir), or a determinism check
        # reports a difference the documents do not have.
        "documents": sorted(str(p.relative_to(out_dir)) for p, _ in emitted),
        "pilot": {"doc_id": "fact-pilot", "facts": pilot_ids,
                  "edges": count_edges(pilot_ids, facts) if pilot_ids else 0},
        "pilot_dense": {"doc_id": "fact-pilot-arith", "facts": pilot2_ids,
                        "edges": count_edges(pilot2_ids, facts) if pilot2_ids else 0},
        "warnings": sorted(warnings),
        "skipped": sorted(skipped),
    }
    write_json(out_dir / "manifest.json", manifest)

    if not args.quiet:
        print(f"facts_to_docir: {len(facts)} facts read, {cards} cards + "
              f"{len(emitted) - cards} index document(s) -> {rel(out_dir)}")
        print(f"  {edges} depends_on edges (0 dangling), {ev_rows} evidence rows; "
              f"fact schema backend: {fv.backend}")
        print(f"  pilot `fact-pilot`: {len(pilot_ids)} facts / "
              f"{manifest['pilot']['edges']} edges; dense alternative "
              f"`fact-pilot-arith`: {len(pilot2_ids)} facts / "
              f"{manifest['pilot_dense']['edges']} edges")
        print(f"  epoch: unix={epoch['unix']} source={epoch['source']}"
              + (f" commit={epoch['commit'][:12]}" if epoch.get("commit") else ""))
        for w in sorted(warnings):
            print(f"  WARNING {w}")
        for s in sorted(skipped):
            print(f"  SKIPPED {s}")

    if out_errors:
        print(f"facts_to_docir: emitted documents FAILED Doc-IR validation "
              f"({len(out_errors)} message(s))", file=sys.stderr)
        for e in out_errors:
            print(f"  ERROR {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
